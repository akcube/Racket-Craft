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
    [(Return exp) (append seq (select-instructions-stmt (Assign (Reg 'rax) exp)))]
    [(Seq stmt tail) (select-instructions-tail tail (append seq (select-instructions-stmt stmt)))]
    )
  )

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(CProgram info (list (cons 'start exp))) (X86Program info (list (cons 'start (Block '() (select-instructions-tail exp '())))))]
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
    ))
