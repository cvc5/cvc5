; COMMAND-LINE: --bv-to-bool
; EXPECT: unsat
(set-logic ALL)
(declare-const x (_ BitVec 1))
(assert true)
(assert (distinct (bvor x (bvashr (_ bv1 1) x)) (bvor x (bvor x (bvashr (_ bv1 1) x)))))
(check-sat)
