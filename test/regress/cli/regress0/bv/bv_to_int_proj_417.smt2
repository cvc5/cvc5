; EXPECT: unsat
(set-logic QF_BV)
(set-option :solve-bv-as-int bitwise)
(declare-const _x15 (_ BitVec 86))
(assert (let ((_let0 (bvcomp _x15 _x15)))(bvugt _let0 _let0)))
(check-sat)
