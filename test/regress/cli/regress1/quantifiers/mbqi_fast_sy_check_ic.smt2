; COMMAND-LINE: --mbqi-fast-sygus --no-cegqi
; EXPECT: unsat
(set-logic BV)
(declare-fun t () (_ BitVec 4))
(declare-fun s () (_ BitVec 4))
(declare-fun xhi () (_ BitVec 4))
(declare-fun xlo () (_ BitVec 4))
(assert (not (= (not (forall ((x (_ BitVec 4))) (or (not (= (bvshl x s) t)) (not (= (bvand xhi x) x)) (not (= (bvor xlo x) x))))) (and (= (bvshl (bvlshr t s) s) t) (= (bvand t (bvshl xhi s)) t) (= (bvor t (bvshl xlo s)) t)))))
(assert true)
(assert (= (bvor xhi (bvnot xlo)) #b1111))
(check-sat)
