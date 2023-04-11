(define (multiply [x : Integer] [y : Integer]) : Integer
  (if (or (= x 0) (= y 0))
      0
      (if (> x 0)
          (+ y (multiply (- x 1) y))
          (- y (multiply (- x 1) (- y))))))


(multiply -2 6)
