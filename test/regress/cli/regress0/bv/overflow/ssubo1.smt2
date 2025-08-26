; EXPECT: unsat
; COMMAND-LINE: 
; COMMAND-LINE: --solve-bv-as-int=sum
(set-logic QF_BV)
(declare-const u (_ BitVec 6))
(declare-const v (_ BitVec 6))
(assert (and (bvsgt v u) (bvslt u #b101011)  (bvsgt v #b010101) (not (bvssubo u v))))
(check-sat)
