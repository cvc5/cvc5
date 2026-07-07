; EXPECT: unsat
(set-logic QF_BVFP)
(declare-const __ (_ BitVec 1))
(set-option :fp-exp true)
(declare-const x RoundingMode)
(check-sat-assuming ((fp.isNaN ((_ to_fp 5 11) x ((_ zero_extend 10) __)))))

