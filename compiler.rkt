#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(require "multigraph.rkt")
(require "priority_queue.rkt")
(provide (all-defined-out))
(require graph)


(define (uniquify_exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body) (let ([n (gensym x)]) (Let n ((uniquify_exp env) e) ((uniquify_exp (dict-set env x n)) body)) )]
      [(Prim op es) (Prim op (for/list ([e es]) ((uniquify_exp env) e)))]
      ))
  )
;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program '() e) (Program '() ((uniquify_exp '()) e))])
  )

;; remove-complex-opera* : R1 -> R1
(define (is-atom? x)
  (or (Int? x)  (Var? x)))

(define (remove-complex-opera* p)
  (match p
    [(Program '() e) (Program '() (remove-complex-opera* e))]
    [(Int n) (Int n)]
    [(Var x) (Var x)]
    [(Let x e body) (Let x (remove-complex-opera* e) (remove-complex-opera* body))]
    [(Prim op es) #:when (< 1 (length es)) (foldl
                                            (lambda (x y)
                                              (match* (x y)
                                                [((? is-atom? rx) (? is-atom? ry)) (Prim op (list ry rx))]
                                                [((? is-atom? rx) ry) (let ([t (gensym 't)]) (Let t (remove-complex-opera* ry) (Prim op (list (Var t) rx))))]
                                                [(rx (? is-atom? ry)) (let ([t (gensym 't)]) (Let t (remove-complex-opera* rx) (Prim op (list ry (Var t)))))]
                                                [(rx ry) (let ([t1 (gensym 't)] [t2 (gensym 't)])
                                                           (Let t1 (remove-complex-opera* ry) (Let t2 (remove-complex-opera* rx) (Prim op (list (Var t1) (Var t2))))))]
                                                )
                                              )
                                            (car es) (cdr es))]
    [(Prim op es) #:when (>= 1 (length es))
                  (match es
                    ['() (Prim op es)]
                    [(list (? is-atom? a)) (Prim op es)]
                    [(list a) (let ([t (gensym 't)]) (Let t (remove-complex-opera* a) (Prim op (list (Var t)))))]
                    )]
    )
  )

;; explicate-control : R1 -> C0
(define (explicate-control-tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Let x rhs body) (explicate-assign rhs x (explicate-control-tail body))]
    [(Prim op es) (Return (Prim op es))]
    [else (error "explicate_tail unhandled case" e)]
    )
  )

(define (explicate-assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Let y rhs body) (explicate-assign rhs y (explicate-assign body x cont))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [else (error "explicate_assign unhandled case" e)]
    )
  )

(define (explicate-control p)
  (match p
    [(Program info body) (CProgram info (list (cons 'start (explicate-control-tail body))))]
    ))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions-atm atm)
  (match atm
    [(Var _) atm]
    [(Int i) (Imm i)]
    )
  )

(define (select-instructions-stmt stmt)
  (match stmt
    [(Assign v exp) (match exp
                      [(? is-atom? exp) (list (Instr 'movq (list (select-instructions-atm exp) v)))]
                      [(Prim 'read '()) (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) v)))]
                      [(Prim '+ (list v1 v2)) (list
                                               (Instr 'movq (list (select-instructions-atm v1) (Reg 'rax)))
                                               (Instr 'addq (list (select-instructions-atm v2) (Reg 'rax)))
                                               (Instr 'movq (list (Reg 'rax) v))
                                               )]
                      [(Prim '- (list v1)) (list
                                            (Instr 'movq (list (select-instructions-atm v1) v))
                                            (Instr 'negq (list v))
                                            )]
                      [(Prim '- (list v1 v2)) (list
                                               (Instr 'movq (list (select-instructions-atm v1) (Reg 'rax)))
                                               (Instr 'subq (list (select-instructions-atm v2) (Reg 'rax)))
                                               (Instr 'movq (list (Reg 'rax) v))
                                               )]
                      )]
    )
  )

(define (select-instructions-tail tail seq)
  (match tail
    [(Return exp) (append seq (select-instructions-stmt (Assign (Reg 'rax) exp)) (list (Jmp 'conclusion)))]
    [(Seq stmt tail) (select-instructions-tail tail (append seq (select-instructions-stmt stmt)))]
    )
  )

(define (select-instructions p)
  (match p
    [(CProgram info (list (cons label exp))) (X86Program info (list (cons label (Block '() (select-instructions-tail exp '())))))]
    ))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (gen-locs locals-types env cnt)
  (match locals-types
    ['() (values env cnt)]
    [(list (cons var 'Integer) rest ...) (gen-locs rest (dict-set env var (+ cnt 8)) (+ cnt 8))]
    )
  )

(define (assign-homes-var env)
  (lambda (var)
    (match var
      [(Imm _) var]
      [(Reg _) var]
      [(Var v) (Deref 'rbp (- (dict-ref env v)))]
      )
    )
  )

(define (assign-homes-instr env)
  (lambda (instr)
    (match instr
      [(Instr name arg*) (Instr name (for/list ([e arg*]) ((assign-homes-var env) e)))]
      [_ instr]
      ))
  )

(define (assign-homes p)
  (match p
    [(X86Program info (list (cons label (Block '() instrs))))
     (let-values
         ([(env cnt) (gen-locs (dict-ref info 'locals-types) '() 0)])
       (X86Program (dict-set info 'stack-space cnt)
                   (list (cons label
                               (Block '()
                                      (for/list ([ins instrs]) ((assign-homes-instr env) ins))
                                      )))))]
    )
  )

;; uncover-live
(define (set-atm atm)
  (match atm
    [(Reg x) (set x)]
    [(Var x) (set x)]
    [(Deref reg v) (set reg)]
    [_ (set)]
    )
  )

(define (list-atm atm)
  (match atm
    [(Reg x) (list x)]
    [(Var x) (list x)]
    [(Deref reg v) (list reg)]
    [_ (list)]
    )
  )

(define (write-set instr)
  (match instr
    [(Instr name args) (set-atm (last args))]
    [_ (set)]
    )
  )

(define (read-set  instr)
  (match instr
    [(Instr 'movq (list r _)) (set-atm r)]
    [(Instr _ args) (foldr set-union (set) (for/list ([arg args]) (set-atm arg)))]
    [(Jmp 'conclusion) (set 'rax 'rsp)]
    [_ (set)]
    )
  )

(define (uncover-live-instrs instrs alist)
  (match instrs
    ['() alist]
    [instrs (uncover-live-instrs
             (cdr instrs)
             (cons (set-union (set-subtract (car alist) (write-set (car instrs))) (read-set (car instrs))) alist)
             )]
    )
  )

(define (uncover-live-block block)
  (match block
    [(Block info instrs) (Block (dict-set info 'live-after (uncover-live-instrs (reverse instrs) (list (set)))) instrs)]
    )
  )

(define (uncover-live p)
  (match p
    [(X86Program info blist)
     (X86Program info (for/list ([block blist]) (cons (car block) (uncover-live-block (cdr block)))))
     ]
    )
  )

;; build-interference :
(define (add-edges G s1 s2 nop)
  (for ([u s1])
    (for ([v s2])
      (cond [(and (not (member u nop)) (not (member u s2))) (add-edge! G u v)]))))

(define (build-interference-aux S G)
  (match S
    [(Block info instrs)
     (let ([live-after (dict-ref info 'live-after)])
       (for/list ([I instrs][L live-after])
         (match I
           [(Instr 'movq (list s d)) (add-edges G L (list-atm d) (list-atm s))]
           [_ (add-edges G L (set->list (write-set I)) '())]
           )
         )
       (Block (dict-remove info 'live-after) instrs))]))

(define (build-interference ast)
  (match ast
    [(X86Program info blocks)
     (define G (undirected-graph '()))
     (for ([var (dict-ref info 'locals-types)])(add-vertex! G (car var)))
     (for ([reg (set->list registers)]) (add-vertex! G reg))
     (define ublocks (for/list ([(label block) (in-dict blocks)]) (cons label (build-interference-aux block G))))
     (define uinfo (dict-set info 'conflicts G))
     (X86Program uinfo ublocks)]))

(define (igviz ast)
  (match ast
    [(X86Program info blocks)
     (graphviz (dict-ref info 'conflicts))])
  )

;; allocate-registers: pseudo-x86 -> pseudo-x86
;;
;;  Register-Color correspondence
;;
;;  Used for register allocation:
;;    0: rcx, 1: rdx, 2: rsi, 3: rdi, 4: r8, 5: r9,
;;    6: r10, 7: rbx, 8: r12, 9: r13, 10: r14, 11+: Stack
;;
;;  Not used for register allocation
;;    -1: rax, -2: rsp, -3: rbp, -4: r11, -5: r15

(define (dsatur-graph-coloring G lvars)

  ; Create necessary datastructures
  (define saturation (make-hash)) ; saturation(u) = {c | ∃v.v ∈ adjacent(u) and color(v) = c}
  (define color (make-hash)) ; color(v) : variable -> color
  (define augment (make-hash)) ; augment(v) : variable -> pq node for key decrements
  (define callee-save-used (mutable-set))
  (define (cmp a b)
    (>= (set-count (hash-ref saturation a)) (set-count (hash-ref saturation b))))
  (define pq (make-pqueue cmp))
  (define max-alloc 0)

  ; Define helper functions
  (define (is-register? r)(set-member? registers r))
  (define (is-var? r)(not (set-member? registers r)))
  (define (init-saturation v)
    (let ([adj-v (filter is-register? (sequence->list (in-neighbors G v)))])
      (hash-set! saturation v (list->set (map register->color adj-v)))))
  (define (upd-saturation-neighbors v)
    (let ([adj-v (filter is-var? (sequence->list (in-neighbors G v)))])
      (for ([u adj-v]) 
        (hash-set! saturation u (set-add (hash-ref saturation u) (hash-ref color v)))
        (pqueue-decrease-key! pq (hash-ref augment u)))))
  (define (set-pmex s)
    (let loop ((n 0)) (if (set-member? s n) (loop (+ n 1)) n)))
  (define (is-callee-reg c)
    (and (>= c 7) (<= c 10)))

  ; Initialize the priority queue and saturation values
  (for ([var lvars])
    (init-saturation (car var))
    (hash-set! augment (car var) (pqueue-push! pq (car var))))

  ; Run DSATUR
  (while (> (pqueue-count pq) 0)
    (let ([v (pqueue-pop! pq)])
      (let ([c (set-pmex (hash-ref saturation v))])
        (set! max-alloc (max max-alloc c)) ; update the value of the highest alloc we had to do
        (hash-set! color v c) ; assign c to color(v)
        (upd-saturation-neighbors v)
        (cond [(is-callee-reg c) (set-add! callee-save-used c)])
        )))

  ; Return
  (values color (max 0 (- max-alloc 10)) callee-save-used))

(define (allocate-registers-atm env)
  (lambda (var)
    (match var
      [(Imm _) var]
      [(Reg _) var]
      [(Var v) (let ([c (dict-ref env v)])
      (cond [(>= c 11)(Deref 'rbp (- (* (- c 6) 8)))]
            [else (Reg (color->register (dict-ref env v)))]
      )
      )]
      )
    )
  )

(define (allocate-registers-instr env)
  (lambda (instr)
    (match instr
      [(Instr name arg*) (Instr name (for/list ([e arg*]) ((allocate-registers-atm env) e)))]
      [_ instr]
      ))
  )

(define (allocate-registers-block env)
  (lambda (block)
    (match block
      [(Block info instrs) (Block info (for/list ([instr instrs]) ((allocate-registers-instr env) instr)))]
    )

  )  
  )

(define (allocate-registers ast)
  (match ast
    [(X86Program info blocks)
      (define-values (color spills callee-save-used) 
        (dsatur-graph-coloring (dict-ref info 'conflicts) (dict-ref info 'locals-types)))
      (define uinfo (dict-set info 'used_callee callee-save-used))
      (X86Program (dict-set uinfo 'stack-space (* spills 8)) 
        (for/list ([block blocks]) (cons (car block) ((allocate-registers-block color) (cdr block))))
      )
    ]
  )
)

;; patch-instructions : psuedo-x86 -> x86
(define (big-int? n)
  (< 65536 n)
  )

(define (patch-instrs instrs)
  (match instrs
    ['() '()]
    [(list ins rest ...)
     (match ins
       [(Instr 'movq (list a a)) (patch-instrs rest)]
       [(Instr name (list (Deref reg1 off1) (Deref reg2 off2)))
        (append (list
                 (Instr 'movq (list (Deref reg1 off1) (Reg 'rax)))
                 (Instr name (list (Reg 'rax) (Deref reg2 off2)))
                 )
                (patch-instrs rest))]
       [(Instr name (list (Imm (? big-int? n)) (Deref reg off)))
        (append (list
                 (Instr 'movq (list (Imm n) (Reg 'rax)))
                 (Instr name (list (Reg 'rax) (Deref reg off)))
                 )
                (patch-instrs rest)
                )]
       ;; This is prolly not required but just in case
       [(Instr name (list (Deref reg off) (Imm (? big-int? n))))
        (append (list
                 (Instr 'movq (list (Deref reg off) (Reg 'rax) ))
                 (Instr name (list (Reg 'rax) (Imm n)))
                 )
                (patch-instrs rest)
                )]
       [_ (cons ins (patch-instrs rest))]
       )
     ]
    )
  )

(define (patch-instructions p)
  (match p
    [(X86Program info (list (cons label (Block '() instrs))))
     (X86Program info (list (cons label (Block '() (patch-instrs instrs)))))
     ]
    )
  )

(define (round-16 n)
  (if (equal? 0 (modulo n 16)) n (* 16 (+ (quotient n 16) 1)))
  )

(define (gen-prelude info)
  (append
   (list
    (Instr 'pushq (list (Reg 'rbp)))
    (Instr 'movq  (list (Reg 'rsp) (Reg 'rbp))))
   ;; Push stuff here
   (for/list ([var (set->list (dict-ref info 'used_callee))])
     (Instr 'pushq (list (Reg (color->register var)))))
  
  (list 
   (Instr 'subq (let [(C (length (set->list (dict-ref info 'used_callee))))]
                  (list (Imm (- (round-16 (+ (dict-ref info 'stack-space) C)) C))
                        (Reg 'rsp))))
   (Jmp 'start)
   ))
  )

(define (gen-conclusion info)
  (append
   (list
    (Instr 'subq (let [(C (length (set->list (dict-ref info 'used_callee))))]
                   (list (Imm (- (round-16 (+ (dict-ref info 'stack-space) C)) C))
                         (Reg 'rsp)))))
   ;; Pop stuff here
   (for/list ([var (reverse (set->list (dict-ref info 'used_callee)))])
     (Instr 'popq (list (Reg (color->register var)))))
    (list 
   (Instr 'popq (list (Reg 'rbp)))
   (Retq))
   )
  )

;; prelude-and-conclusion : x86 -> x86
(define (main-block)
  (match (system-type 'os)
    ['macos '_main]
    [_ 'main]
    )
  )

(define (prelude-and-conclusion p)
  (match p
    [(X86Program info (list (cons label (Block '() instrs))))
     (X86Program info (list
                       (cons label (Block '() instrs))
                       (cons (main-block) (Block '() (gen-prelude info)))
                       (cons 'conclusion (Block '() (gen-conclusion info)))
                       ))]
    ))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
    ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
    ("instruction selection" ,select-instructions , interp-x86-0)
    ("uncover live", uncover-live, interp-x86-0)
    ("build interference", build-interference, interp-x86-0)
    ("allocate registers", allocate-registers, interp-x86-0)
    ; ("vis", igviz)
    ; ("assign homes" ,assign-homes ,interp-x86-0)
    ("patch instructions" ,patch-instructions ,interp-x86-0)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
    ))
