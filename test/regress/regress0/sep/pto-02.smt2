(set-logic QF_ALL)
(set-info :status unsat)
(declare-heap (Int Int))


(declare-const x Int)

(declare-const a1 Int)
(declare-const a2 Int)
(declare-const a3 Int)
(declare-const a4 Int)
(declare-const a5 Int)
(declare-const a6 Int)
(declare-const a7 Int)
(declare-const a8 Int)
(declare-const a9 Int)

(assert (and (pto x a1) (pto x a2) (pto x a3) 
         (pto x a4) (pto x a5) (pto x a6)
         (pto x a7) (pto x a8) (pto x a9)
    )
)

(assert (not (= a1 a2 a3 a4 a5 a6 a7 a8 a9)))

(check-sat)
