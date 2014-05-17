; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
(set-logic QF_ABV)
(declare-fun b () (_ BitVec 32))
(declare-fun hk () (Array Bool (_ BitVec 32)))
(push 1)
(assert (not (= b (select hk true))))
(check-sat)
(pop 1)
(assert (not (= b (_ bv0 32))))
(assert (= b (select hk true)))
(check-sat)
