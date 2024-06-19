; EXPECT: sat
; EXPECT: sat

(set-logic QF_BV)
(set-option :incremental true)
(set-option :solve-bv-as-int sum)

(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun z () (_ BitVec 4))

(assert (= x y))
(check-sat)
(push 1)
(assert (= y z))
(check-sat)
(pop 1)

