(define (is-positive [x : Integer]) : Boolean (>= x 0))

(if (is-positive -10) 42 0)