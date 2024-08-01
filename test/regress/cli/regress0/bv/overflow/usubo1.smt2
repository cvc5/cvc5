; EXPECT: unsat
; COMMAND-LINE: 
; COMMAND-LINE: --solve-bv-as-int=sum
(set-logic QF_BV)
(declare-const u (_ BitVec 6))
(declare-const v (_ BitVec 6))
(assert (and (bvugt v u) (not (bvusubo u v))))
(check-sat)
