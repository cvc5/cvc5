; COMMAND-LINE: -i --bv-solver=bitblast --bv-assert-input
(set-logic QF_BV)
(declare-fun N () Bool)
(assert (not (= (_ bv1 1) (bvnot (ite N (_ bv1 1) (_ bv0 1))))))
(push 1)
(assert (not N))
(set-info :status unsat)
(check-sat)
(pop 1)
(set-info :status sat)
(check-sat)

