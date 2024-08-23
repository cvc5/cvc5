; COMMAND-LINE: --uf-lambda-qe -q
; EXPECT: sat
(set-logic HO_ALL)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun S () (Set (_ BitVec 32)))
(assert (not (= (set.filter (lambda ((x (_ BitVec 32))) (bvult x a)) S) (set.filter (lambda ((x (_ BitVec 32))) (bvult x b)) S))))
(check-sat)
