; EXPECT: (error "Parse Error: issue4437-unc-quant.smt2:6.15: Quantifier used in non-quantified logic.")
; EXIT: 1
(set-logic QF_AUFBVLIA)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (forall ((c (_ BitVec 8))) (= (bvashr c a) b)))
(check-sat)
