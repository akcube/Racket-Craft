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
(provide (all-defined-out))


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

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info body) (CProgram info (list (cons 'start (explicate-control-tail body))))]
    ))


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
                      [(Prim 'read '()) (list (Callq 'read_int 1) (Instr 'movq (list (Reg 'rax) v)))]
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

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(CProgram info (list (cons label exp))) (X86Program info (list (cons label (Block '() (select-instructions-tail exp '())))))]
    ))

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

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  ; (error "TODO: code goes here (assign-homes)"))
  (match p
    [(X86Program info (list (cons label (Block '() instrs))))
     (let-values
         ([(env cnt) (gen-locs (dict-ref info 'locals-types) '() 0)])
       (X86Program (dict-set info 'stack-space cnt)
                   (list (cons label
                               (Block '()
                                      (for/list ([ins instrs]) ((assign-homes-instr env) ins))
                                      )))))]
    ))

(define (big-int? n)
  (< 65536 n)
  )

(define (patch-instrs instrs)
  (match instrs
    ['() '()]
    [(list ins rest ...)
     (match ins
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

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  ; (error "TODO: code goes here (patch-instructions)"))
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
  (list
   (Instr 'pushq (list (Reg 'rbp)))
   (Instr 'movq  (list (Reg 'rsp) (Reg 'rbp)))
   (Instr 'subq  (list (Imm (round-16 (dict-ref info 'stack-space))) (Reg 'rsp)))
   (Jmp 'start)
   )
  )

(define (gen-conclusion info)
  (list
   (Instr 'addq (list (Imm (round-16 (dict-ref info 'stack-space))) (Reg 'rsp)))
   (Instr 'popq (list (Reg 'rbp)))
   (Retq)
   )
  )

(define (main-block)
  (match (system-type 'os)
    ['macos '_main]
    [_ 'main]
  )
)

;; prelude-and-conclusion : x86 -> x86
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
    ;; Uncomment the following passes as you finish them.
    ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
    ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
    ("instruction selection" ,select-instructions , interp-x86-0)
    ("assign homes" ,assign-homes ,interp-x86-0)
    ("patch instructions" ,patch-instructions ,interp-x86-0)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
    ))
