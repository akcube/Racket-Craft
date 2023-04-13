(define (absolute [x : Integer]) : Integer
  (if (< x 0)
      (- x)
      x))

(define (largest_absolute [x : Integer] [y : Integer]) : Integer
  (let ([abs-x (absolute x)])
    (let ([abs-y (absolute y)]) 
      (if (> abs-x abs-y)
        abs-x
        abs-y))))

(largest_absolute -7 -1)