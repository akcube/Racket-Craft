(define (find-max [a : Integer] [b : Integer] [c : Integer]) : Integer
  (let ([max-ab (if (> a b) a b)])
    (if (> max-ab c)
        max-ab
        c)))

(find-max 1 2 3)
