; COMMAND-LINE: --solve-bv-as-int=sum
; EXPECT: sat

(set-logic QF_BV)

(declare-fun zero () (_ BitVec 16))
(declare-fun x () (_ BitVec 16))

(assert (= zero (_ bv0 16)))
(assert (= zero (bvneg x)))

(check-sat)
