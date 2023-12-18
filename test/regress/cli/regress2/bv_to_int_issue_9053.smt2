; COMMAND-LINE: --solve-bv-as=iand --check-models
; EXPECT: sat
(set-logic ALL)
(declare-fun a () (Array Int Int))
(declare-fun b ((_ BitVec 3)) Int)
(declare-fun c () (_ BitVec 3))
(declare-fun d () (_ BitVec 3))
(assert (distinct (select a (b (bvand c d))) (select a (b (bvor c d)))))
(check-sat)
