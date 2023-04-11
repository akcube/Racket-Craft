(define (is-positive [x : Integer]) : Boolean
  (if (>= x 0)
      #t
      #f))

(is-positive -10)