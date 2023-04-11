(define (is-positive [x : Integer]) : Integer
  (if (>= x 0)
      1
      0))

(is-positive -10)