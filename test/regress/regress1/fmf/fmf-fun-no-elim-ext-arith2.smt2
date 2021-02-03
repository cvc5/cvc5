; COMMAND-LINE: --fmf-fun --no-check-models
; EXPECT: sat
(set-logic UFNIA)
(set-info :status sat)
(define-fun-rec int-and ((n Int) (n1 Int) (n2 Int)) Bool (
    or
    (= n1 n 0)
    (= n2 n 0)
    (
        and
        (> n1 0)
        (> n2 0)
        (>= n 0)
        (= (not (= (mod n 2 ) 0)) (and (not (= (mod n1 2 ) 0)) (not (= (mod n2 2) 0))))
        (int-and (div n 2) (div n1 2) (div n2 2))
    )
))
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (= x 1))
(assert (= y 1))
(assert (= z 1))
(assert (int-and z x y))
(check-sat)
