; COMMAND-LINE: --solve-bv-as-int=1 --no-check-models  --no-check-unsat-cores
; EXPECT: sat
(set-logic QF_BV)
(declare-fun addr_0x130ef30 () (_ BitVec 63))
(assert (distinct addr_0x130ef30 (_ bv0 63)))
(check-sat)
(exit)
