; EXPECT: unsat
; EXPECT: (
; EXPECT: a0
; EXPECT: )
(set-logic QF_BV)
(declare-const __ (_ BitVec 1))
(set-option :unsat-cores-mode sat-proof)
(assert (! (bvsgt __ __) :named a0))
(check-sat)
(get-unsat-core)