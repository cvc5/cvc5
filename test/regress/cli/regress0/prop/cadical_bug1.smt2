; COMMAND-LINE: -i --sat-solver=cadical
; DISABLE-TESTER: proof
(set-logic BV)
(declare-const c (_ BitVec 1))
(assert (forall ((m (_ BitVec 32))) (distinct (_ bv0 32) (bvadd ((_ zero_extend 31) c) (bvmul m (_ bv2 32))))))
(push 1)
(set-info :status sat)
(check-sat)
(pop 1)
(assert (exists ((m (_ BitVec 32))) (not (distinct (_ bv0 32) ((_ zero_extend 31) c)))))
(set-info :status unsat)
(check-sat)
