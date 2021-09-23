; EXPECT: sat
(set-logic ALIA)
(define-sort Stream (T) (Array Int T))
(define-sort IntStream () (Stream Int))
(check-sat)
