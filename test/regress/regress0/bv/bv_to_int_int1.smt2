; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=1
; EXPECT: sat
(set-logic QF_ALL)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun z () Int)
(declare-fun w () Int)
(assert (= x (_ bv3 4)))
(assert (= y (_ bv3 4)))
(assert (> z w))
(check-sat)
