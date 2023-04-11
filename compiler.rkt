#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
; (require "interp-Lint.rkt")
(require "interp-Lif.rkt")
(require "interp-Lvar.rkt")
(require "interp-Lfun.rkt")
(require "interp-Lfun-prime.rkt")
(require "interp-Cvar.rkt")
(require "interp-Cif.rkt")
(require "interp-Cfun.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Lfun.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Cif.rkt")
(require "type-check-Cfun.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(require "multigraph.rkt")
(require "priority_queue.rkt")
(provide (all-defined-out))
(require graph)

;; Shrink pass
(define (shrink-exp e)
  (match e
    [(Prim 'and (list a b)) (If (shrink-exp a) (shrink-exp b) (Bool #f))]
    [(Prim 'or  (list a b)) (If (shrink-exp a) (Bool #t) (shrink-exp b))]
    [(Let x e body) (Let x (shrink-exp e) (shrink-exp body))]
    [(Prim op es) (Prim op (map shrink-exp es))]
    [(If cond a b) (If (shrink-exp cond) (shrink-exp a) (shrink-exp b))]
    [_ e]
    )
  )

(define (shrink-def def)
  (match def
    [(Def name param-list rty info body) (Def name param-list rty info (shrink-exp body))]
    )
  )

(define (shrink p)
  (match p
    [(ProgramDefsExp info defs exp)
     (ProgramDefs info
                  (append
                   (for/list ([def defs]) (shrink-def def))
                   (list (Def 'main '() 'Integer '() (shrink-exp exp)))
                   ))]
    [_ (error "shrink: not a ProgramDefsExp")]
    )
  )

;; Uniquify pass
(define (uniquify_exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Let x e body) (let ([n (gensym x)]) (Let n ((uniquify_exp env) e) ((uniquify_exp (dict-set env x n)) body)) )]
      [(Prim op es) (Prim op (for/list ([e es]) ((uniquify_exp env) e)))]
      [(If cond a b) (If ((uniquify_exp env) cond) ((uniquify_exp env) a) ((uniquify_exp env) b))]
      [(Apply f exp) (Apply ((uniquify_exp env) f) (map (uniquify_exp env) exp))]
      ))
  )

(define (extract-var var)
  (match var
    [(quasiquote [,x : ,_]) x]
    )
  )

(define (extract-def-name def)
  (match def
    [(Def name _ _ _ _) name]
    )
  )

(define (uniquify-def env)
  (lambda (def)
    (match def
      [(Def name param-list rty info body)
       (define new-env (append (for/list ([x param-list]) (let ([y (extract-var x)]) (cons y (gensym y)))) env))
       (Def (dict-ref env name)
            (for/list ([x param-list]) (match x [(quasiquote [,x : ,t])  `[,(dict-ref new-env x) :,t]]))
            rty info
            ((uniquify_exp
              new-env
              ) body))]
      ))
  )

(define (uniquify p)
  (match p
    [(ProgramDefs info defs)
     (define env (for/list [(d defs)] (define name (extract-def-name d)) (cons name (cond [(eq? name 'main) name] [else (gensym name)]))))
     (ProgramDefs info (map (uniquify-def env) defs))
     ])
  )

(define (reveal-functions-exp funcs)
  (lambda (e)
    (match e
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Var v) (if (assq v funcs) (FunRef (car (assq v funcs)) (cdr (assq v funcs))) (Var v))]
      [(Prim op es) (Prim op (map (reveal-functions-exp funcs) es))]
      [(Let x e body) (Let x ((reveal-functions-exp funcs) e) ((reveal-functions-exp funcs) body))]
      [(If cond a b) (If ((reveal-functions-exp funcs) cond) ((reveal-functions-exp funcs) a) ((reveal-functions-exp funcs) b))]
      [(Apply f exp) (Apply ((reveal-functions-exp funcs) f) (map (reveal-functions-exp funcs) exp))]
      )
    )
  )

(define (reveal-functions-def funcs)
  (lambda (def)
    (match def
      [(Def name param-list rty info body)
       (Def name param-list rty info ((reveal-functions-exp funcs) body))
       ]
      )
    )
  )

(define (reveal-functions p)
  (match p
    [(ProgramDefs info defs)
     (define funcs (for/list ([def defs]) (match def [(Def name param-list _ _ _) (cons name (length param-list))])))
     (ProgramDefs info (map (reveal-functions-def funcs) defs))
     ]
    )
  )

;; remove-complex-opera* : R1 -> R1
(define (is-atom? x)
  (or (Int? x) (Var? x) (Bool? x)))

(define (rec-let args gen-names inner-fn)
  (if (null? args)
      (let ([t (gensym 't)] ) (Let t inner-fn (Apply (Var t) gen-names)))
      (let ([t (gensym 't)])
        (Let t (car args) (rec-let (cdr args) (append gen-names (list (Var t))) inner-fn)))))

(define (remove-complex-opera* p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map remove-complex-opera* defs))]
    [(Def name param-list rty info body) (Def name param-list rty info (remove-complex-opera* body))]
    [(Int n) (Int n)]
    [(Var x) (Var x)]
    [(Bool b) (Bool b)]
    [(FunRef label kargs) (FunRef label kargs)]
    [(Let x e body) (Let x (remove-complex-opera* e) (remove-complex-opera* body))]
    [(If con tru els) (If (remove-complex-opera* con) (remove-complex-opera* tru) (remove-complex-opera* els))]
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
    [(Apply f exp) (rec-let exp '() f)]
    )
  )

;; explicate-control : R1 -> C0
(define (explicate-control-tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Bool b) (Return (Bool b))]
    [(Let x rhs body) (explicate-assign rhs x (explicate-control-tail body))]
    [(Prim op es) (Return (Prim op es))]
    [(If cnd thn els) (explicate-pred cnd (explicate-control-tail thn)
                                      (explicate-control-tail els))]
    [(Apply f exp) (TailCall f exp)]
    [_ (error "explicate_tail unhandled case" e)]
    )
  )

(define (explicate-assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Bool b) (Seq (Assign (Var x) (Bool b)) cont)]
    [(Let y rhs body) (explicate-assign rhs y (explicate-assign body x cont))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [(If cnd thn els) (explicate-pred cnd (explicate-assign thn x cont)
                                      (explicate-assign els x cont))]
    [(Apply f exp) (Seq (Assign (Var x) (Call f exp))  cont)]
    [(FunRef label kargs) (Seq (Assign (Var x) (FunRef label kargs)) cont)]
    [_ (error "explicate_assign unhandled case" e)]
    )
  )

(define (explicate-pred cnd thn els)
  (match cnd
    [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) (create_block thn)
                     (create_block els))]
    [(Let x rhs body) (explicate-assign rhs x (explicate-pred body thn els))]
    [(Prim 'not (list e)) (IfStmt (Prim 'eq? (list e (Bool #f))) (create_block thn)
                                  (create_block els))]
    [(Prim op es) #:when (or (eq? op 'eq?) (eq? op '<) (eq? op '>) (eq? op '<=) (eq? op '>=))
                  (IfStmt (Prim op es) (create_block thn)
                          (create_block els))]
    [(Bool b) (if b thn els)]
    [(If cnd^ thn^ els^) (explicate-pred cnd^ (explicate-pred thn^ thn els)
                                         (explicate-pred els^ thn els))]
    [(Apply f exp) (let ([pred (gensym 'pred)])
                     (Seq (Assign (Var pred) (Call f exp))
                          (IfStmt (Prim 'eq? (list (Var pred) (Bool #t))) (create_block thn) (create_block els))))]
    [_ (error "explicate_pred unhandled case" cnd)]))

(define basic-blocks '())

(define (create_block tail)
  (match tail
    [(Goto label) (Goto label)]
    [_
     (let ([label (gensym 'block)])
       (set! basic-blocks (cons (cons label tail) basic-blocks))
       (Goto label))]))

(define (explicate-control-def defs)
  (match defs
    [(Def name param-list rty info body)
     (set! basic-blocks '())
     (let ([tail (explicate-control-tail body)])
       (Def name param-list rty info (dict-set basic-blocks (symbol-append name 'start) tail)))]))


(define (explicate-control p)
  (set! basic-blocks '())
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map explicate-control-def defs))]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions-atm atm)
  (match atm
    [(Var _) atm]
    [(Int i) (Imm i)]
    [(Bool b) (Imm (if b 1 0))]
    )
  )

(define (select-instructions-stmt stmt)
  (match stmt
    [(Assign v exp) (match exp
                      [(? is-atom? exp) (list (Instr 'movq (list (select-instructions-atm exp) v)))]
                      [(FunRef f n) (list (Instr 'leaq (list (Global f) v)))]
                      [(Call f ps) (append (for/list ([v ps] [reg arg-registers]) (Instr 'movq (list v (Reg reg))))
                                           (list (IndirectCallq f (length ps)) (Instr 'movq (list (Reg 'rax) v))))]
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
                      [(Prim 'not (list v1)) #:when (eq? v1 v)  (list
                                                                 (Instr 'xorq (list (Imm 1) v))
                                                                 )]
                      [(Prim 'not (list v1)) (list
                                              (Instr 'movq (list (select-instructions-atm v1) v))
                                              (Instr 'xorq (list (Imm 1) v))
                                              )]
                      [(Prim 'eq? (list v1 v2)) (list
                                                 (Instr 'cmpq (list (select-instructions-atm v1) (select-instructions-atm v2)))
                                                 (Instr 'set (list 'e (ByteReg 'al)))
                                                 (Instr 'movzbq (list (ByteReg 'al) v))
                                                 )]
                      [(Prim '< (list v1 v2)) (list
                                               (Instr 'cmpq (list (select-instructions-atm v2) (select-instructions-atm v1)))
                                               (Instr 'set (list 'l (ByteReg 'al)))
                                               (Instr 'movzbq (list (ByteReg 'al) v))
                                               )]
                      [(Prim '> (list v1 v2)) (list
                                               (Instr 'cmpq (list (select-instructions-atm v2) (select-instructions-atm v1)))
                                               (Instr 'set (list 'g (ByteReg 'al)))
                                               (Instr 'movzbq (list (ByteReg 'al) v))
                                               )]
                      [(Prim '<= (list v1 v2)) (list
                                                (Instr 'cmpq (list (select-instructions-atm v2) (select-instructions-atm v1)))
                                                (Instr 'set (list 'le (ByteReg 'al)))
                                                (Instr 'movzbq (list (ByteReg 'al) v))
                                                )]
                      [(Prim '>= (list v1 v2)) (list
                                                (Instr 'cmpq (list (select-instructions-atm v2) (select-instructions-atm v1)))
                                                (Instr 'set (list 'ge (ByteReg 'al)))
                                                (Instr 'movzbq (list (ByteReg 'al) v))
                                                )]
                      )]
    )
  )

(define (select-instructions-tail tail seq name)
  (match tail
    [(Return exp) (append seq (select-instructions-stmt (Assign (Reg 'rax) exp)) (list (Jmp (symbol-append name 'conclusion))))]
    [(TailCall f ps) (append seq (for/list ([v ps] [reg arg-registers]) (Instr 'movq (list v (Reg reg))))
                             (list (TailJmp f (length ps))))]
    [(Goto label) (append seq (list (Jmp label)))]
    [(IfStmt (Prim 'eq? (list v1 v2)) (Goto thn) (Goto els)) (append seq (list (Instr 'cmpq (list (select-instructions-atm v2) (select-instructions-atm v1))) (JmpIf 'e thn) (Jmp els)))]
    [(IfStmt (Prim '< (list v1 v2)) (Goto thn) (Goto els)) (append seq (list (Instr 'cmpq (list (select-instructions-atm v2) (select-instructions-atm v1))) (JmpIf 'l thn) (Jmp els)))]
    [(IfStmt (Prim '> (list v1 v2)) (Goto thn) (Goto els)) (append seq (list (Instr 'cmpq (list (select-instructions-atm v2) (select-instructions-atm v1))) (JmpIf 'g thn) (Jmp els)))]
    [(IfStmt (Prim '>= (list v1 v2)) (Goto thn) (Goto els)) (append seq (list (Instr 'cmpq (list (select-instructions-atm v2) (select-instructions-atm v1))) (JmpIf 'le thn) (Jmp els)))]
    [(IfStmt (Prim '<= (list v1 v2)) (Goto thn) (Goto els)) (append seq (list (Instr 'cmpq (list (select-instructions-atm v2) (select-instructions-atm v1))) (JmpIf 'ge thn) (Jmp els)))]
    [(Seq stmt tail) (select-instructions-tail tail (append seq (select-instructions-stmt stmt)) name)]
    )
  )

(define (update-start-block blocks name param-list)
  (define start-block (dict-ref blocks (symbol-append name 'start)))
  (define new-start (match start-block
                      [(Block info tail)
                       (Block info (append
                                    (for/list ([v param-list] [reg arg-registers]) (Instr 'movq (list (Reg reg) (Var (extract-var v)))))
                                    tail
                                    ))]))
  (dict-set blocks (symbol-append name 'start) new-start)
  )

(define (select-instructions-def def)
  (match def
    [(Def name param-list rty info blocks)
     (Def name '() 'Integer (dict-set info 'num-params (length param-list))
          (update-start-block (for/list ([(label tail) (in-dict blocks)])
                                (cons label (Block '() (select-instructions-tail tail '() name)))) name param-list))
     ]
    )
  )

(define (select-instructions p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map select-instructions-def defs))]
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
    [(FunRef label kargs) (FunRef label kargs)]
    [(Reg x) (set x)]
    [(ByteReg x) (set x)]
    [(Var x) (set x)]
    [(Deref reg v) (set reg)]
    [_ (set)]
    )
  )

(define (list-atm atm)
  (match atm
    [(FunRef label kargs) (FunRef label kargs)]
    [(Reg x) (list x)]
    [(ByteReg x) (list x)]
    [(Var x) (list x)]
    [(Deref reg v) (list reg)]
    [_ (list)]
    )
  )

(define (write-set instr)
  (match instr
    [(IndirectCallq addr num-args) (caller-save-for-alloc)]
    [(Callq addr num-args) (set)] ; only read_int?
    [(TailJmp addr num-args) (caller-save-for-alloc)]
    [(Instr 'leaq (list r _)) (set-atm r)]
    [(Jmp label) (set)]
    [(JmpIf cc label) (set)]
    [(Instr 'cmpq _) (set)]
    [(Instr 'set _) (set)]
    [(Instr 'movzbq (list s d)) (set-atm d)]
    [(Instr name args) (set-atm (last args))]
    [_ (set)]
    )
  )

(define (read-set  instr)
  (match instr
    [(Instr 'leaq (list s d)) (set-atm s)]
    [(IndirectCallq addr num-args)
     (set-union (set-atm addr) (vector->set (vector-take arg-registers num-args)))]
    [(Callq addr num-args) (set)] ; only read_int?
    [(TailJmp addr num-args)
     (set-union (set-atm addr) (vector->set (vector-take arg-registers num-args)))]
    [(Jmp 'conclusion) (set 'rax 'rsp)]
    [(Jmp label) (set)]
    [(JmpIf cc label) (set)]
    [(Instr 'movq (list r _)) (set-atm r)]
    [(Instr 'movzbq (list s d)) (set)]
    [(Instr 'set _) (set)]
    [(Instr _ args) (foldr set-union (set) (for/list ([arg args]) (set-atm arg)))]
    [_ (set)]
    )
  )

(define (live-before label computed-live)
  (cond [(string-suffix? (symbol->string label) "conclusion") (set)]
        [else (match (hash-ref computed-live label)
                [(Block info ss) (car (dict-ref info 'live-after))])]))

(define (uncover-live-instrs instrs computed-live alist)
  (match instrs
    ['() alist]
    [_ (uncover-live-instrs
        (cdr instrs)
        computed-live
        (match (car instrs)
          [(Jmp label) (cons (live-before label computed-live) alist)]
          [(JmpIf cc label) (cons (set-union (car alist) (live-before label computed-live)) alist)]
          [_ (cons (set-union (set-subtract (car alist) (write-set (car instrs))) (read-set (car instrs))) alist)]
          ))]))

(define (uncover-live-block block computed-live)
  (match block
    [(Block info instrs) (Block (dict-set info 'live-after (uncover-live-instrs (reverse instrs) computed-live (list (set)))) instrs)]))

(define (uncover-live-blocks blist bgraph)
  (define CFG-hash (make-hash))
  (for ([label (tsort (transpose bgraph))])
    (hash-set! CFG-hash label (uncover-live-block (dict-ref blist label) CFG-hash)))
  (hash->list CFG-hash))

(define (get-liveset label)
  (cond [(string-suffix? (symbol->string label) "conclusion") (set)]
        [else (set label)]))

(define (out-blocks p)
  (match p
    [(Block info instrs) (for/fold ([oblks (set)]) ([inst instrs]) (set-union oblks (out-blocks inst)))]
    [(JmpIf cc label) (get-liveset label)]
    [(Jmp label) (get-liveset label)]
    [_ (set)]))

(define (make-cfg blist)
  (define G (directed-graph '()))
  (for ([label (in-dict-keys blist)]) (add-vertex! G label))
  (for ([(u block) (in-dict blist)])
    (for ([v (out-blocks block)]) (add-directed-edge! G u v)))
  G)

(define (uncover-live p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map uncover-live defs))]
    [(Def name param-list rty info blist)
     (Def name param-list rty info (uncover-live-blocks blist (make-cfg blist)))]))

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
           [(Instr 'movzbq (list s d)) (add-edges G L (list-atm d) (list-atm s))]
           [(Callq addr num-args) (add-edges G L (set->list caller-save-for-alloc) '())]
           [(Instr 'set _) '()]
           [_ (add-edges G L (set->list (write-set I)) '())]
           )
         )
       (Block (dict-remove info 'live-after) instrs))]))

(define (build-interference ast)
  (match ast
    [(ProgramDefs info defs) (ProgramDefs info (map build-interference defs))]
    [(Def name param-list rty info blocks)
     (define G (undirected-graph '()))
     (for ([var (dict-ref info 'locals-types)])(add-vertex! G (car var)))
     (for ([reg (set->list registers)]) (add-vertex! G reg))
     (define ublocks (for/list ([(label block) (in-dict blocks)]) (cons label (build-interference-aux block G))))
     (define uinfo (dict-set info 'conflicts G))
     (Def name param-list rty uinfo ublocks)]))

(define (igviz ast)
  (match ast
    [(ProgramDefs info defs) (ProgramDefs info (map igviz defs))]
    [(Def name param-list rty info blocks)
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
      [(ByteReg _) var]
      [(Var v) (let ([c (dict-ref env v)])
                 (cond [(>= c 11)(Deref 'rbp (- (* (- c 6) 8)))]
                       [else (Reg (color->register c))]
                       )
                 )]
      [_ var]
      )
    )
  )

(define (allocate-registers-instr env)
  (lambda (instr)
    (match instr
      [(Instr 'set _) instr]
      [(Instr name arg*) (Instr name (for/list ([e arg*]) ((allocate-registers-atm env) e)))]
      [(TailJmp var ar) (TailJmp ((allocate-registers-atm env) var) ar)]
      [(Callq var ar) (Callq ((allocate-registers-atm env) var) ar)]
      [(IndirectCallq var ar) (IndirectCallq ((allocate-registers-atm env) var) ar)]
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
    [(ProgramDefs info defs) (ProgramDefs info (map allocate-registers defs))]
    [(Def name param-list rty info blocks)
     (define-values (color spills callee-save-used)
       (dsatur-graph-coloring (dict-ref info 'conflicts) (dict-ref info 'locals-types)))
     (define uinfo (dict-set info 'used_callee callee-save-used))
     (Def name param-list rty (dict-set uinfo 'stack-space (* spills 8))
          (for/list ([block blocks]) (cons (car block) ((allocate-registers-block color) (cdr block)))))]))

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

(define (patch-instrs-block b)
  (match b
    [(Block info instrs) (Block info (patch-instrs instrs))]
    )
  )

(define (patch-instrs-def d)
  (match d
    [(Def name param-list rty info blocks)
     (Def name param-list rty info (for/list ([(label block) (in-dict blocks)]) (cons label (patch-instrs-block block))))]
    )
)

(define (patch-instructions p)
  (match p
    [(ProgramDefs info defs)
     (ProgramDefs info (for/list ([def defs]) (patch-instrs-def def)))
     ]
    )
  )

;; prelude-and-conclusion : x86 -> x86
(define (round-16 n)
  (if (equal? 0 (modulo n 16)) n (* 16 (+ (quotient n 16) 1)))
  )

(define (gen-prelude name info)
  (Block '() (append
              (list
               (Instr 'pushq (list (Reg 'rbp)))
               (Instr 'movq  (list (Reg 'rsp) (Reg 'rbp))))
              ;; Push stuff here
              (for/list ([var (set->list (dict-ref info 'used_callee))])
                (Instr 'pushq (list (Reg (color->register var)))))

              (list
               (Instr 'subq (let [(C (* 8 (length (set->list (dict-ref info 'used_callee)))))]
                              (list (Imm (- (round-16 (+ (dict-ref info 'stack-space) C)) C))
                                    (Reg 'rsp))))
               (Jmp (symbol-append name 'start))
               )))
  )

(define (gen-conclusion info)
  (Block '() (append
              (list
               (Instr 'addq (let [(C (* 8 (length (set->list (dict-ref info 'used_callee)))))]
                              (list (Imm (- (round-16 (+ (dict-ref info 'stack-space) C)) C))
                                    (Reg 'rsp)))))
              ;; Pop stuff here
              (for/list ([var (reverse (set->list (dict-ref info 'used_callee)))])
                (Instr 'popq (list (Reg (color->register var)))))
              (list
               (Instr 'popq (list (Reg 'rbp)))
               (Retq))
              )))

(define (main-block)
  (match (system-type 'os)
    ['macos '_main]
    [_ 'main]
    )
  )

(define (prelude-and-conclusion p)
  (match p
    [(ProgramDefs info defs)
     (ProgramDefs info
                  (for/list ([def defs])
                    (match def
                      [(Def name param-list rty info blocks)
                       (Def name param-list rty info
                            (append blocks (list (cons name (gen-prelude name info)) (cons (symbol-append name 'conclusion) (gen-conclusion info)))))]
                      [_ def]
                      )
                    )
                  )]
     ))

(define (print-as p)
  (pretty-print p)
  p
  )

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ("shrink", shrink, interp-Lfun, type-check-Lfun)
    ("uniquify", uniquify, interp-Lfun, type-check-Lfun)
    ("reveal functions", reveal-functions, interp-Lfun-prime, type-check-Lfun)
    ("remove complex opera*", remove-complex-opera*, interp-Lfun-prime, type-check-Lfun)
    ("explicate control", explicate-control, interp-Cfun, type-check-Cfun)
    ; ("printer", print-as, interp-Cfun, type-check-Cfun)
    ("instruction selection" ,select-instructions, interp-pseudo-x86-3)
    ("uncover live", uncover-live, interp-pseudo-x86-3)
    ("build interference", build-interference, interp-pseudo-x86-3)
    ("allocate registers", allocate-registers, interp-x86-3)
    ("patch instructions" ,patch-instructions ,interp-x86-3)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-3)
    ; ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
    ; ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
    ; ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
    ; ("instruction selection" ,select-instructions , interp-x86-0)
    ; ("vis", igviz, interp-pseudo-x86-3)
    ; ; ("assign homes" ,assign-homes ,interp-x86-0)
    ))
