#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "compiler.rkt")

(define file (command-line #:args (filename) filename))
(define ast (read-program file))

; (debug-level 2)
(AST-output-syntax 'concrete-syntax)

(define (opt passes ast)
  (pretty-print ast)
  (match passes
    ['() ast]
    [(list (list name fun interp type-check) more ...)
     (println (string-append "Applying " name))
     (opt more (type-check (fun ast)))]
    [(list (list name fun interp) more ...)
     (println (string-append "Applying " name))
     (opt more (fun ast))]
    [(list (list name fun) more ...)
     (println (string-append "Applying " name))
     (opt more (fun ast))]))

(define final (opt compiler-passes ast))
