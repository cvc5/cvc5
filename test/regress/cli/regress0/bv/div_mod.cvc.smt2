; DISABLE-TESTER: lfsc
; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () (_ BitVec 4))
(check-sat-assuming ( (not (let ((_let_1 (bvsdiv x #b0000))) (and (and (and (and (= (bvudiv x #b0000) #b1111) (= (bvurem x #b0000) x)) (or (= _let_1 #b1111) (= _let_1 #b0001))) (= (bvsrem x #b0000) x)) (= (bvsmod x #b0000) x)))) ))
