(set-logic BV)
(set-info :status unsat)
(assert (exists ((?y2 (_ BitVec 32))) (exists ((?y3 (_ BitVec 32))) (forall ((?y5 (_ BitVec 32))) (forall ((?y6 (_ BitVec 32))) (not (= (bvadd (bvadd (bvadd (bvadd (bvmul (bvneg (_ bv65 32)) ?y6) (bvmul (bvneg (_ bv93 32)) ?y5)) (_ bv0 32)) (_ bv0 32)) (_ bv0 32)) (_ bv69 32))))))))
(check-sat)
