(define (double [x : Integer]) : Integer
  (+ x 2))

(define (triple_and_double [x : Integer]) : Integer
  (+ (+ x 3) (double x)))

(triple_and_double 5)
