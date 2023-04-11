(define (factorial [n : Integer]) : Integer
  (if (eq? n 0)
      1
      (* n (factorial (- n 1)))))

(factorial 5)
