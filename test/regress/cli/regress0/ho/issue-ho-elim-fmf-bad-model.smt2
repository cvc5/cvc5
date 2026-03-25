; COMMAND-LINE: --ho-elim --finite-model-find --uf-ss=no-minimal --debug-check-models
; EXPECT: sat
; EXIT: 0
(set-logic HO_ALL)
(declare-sort beverage 0)
(declare-sort syrup 0)
(declare-fun hot (beverage) Bool)
(assert (not (exists ((Mixture (-> syrup beverage))) (not (exists ((S syrup)) (let ((_let_1 (Mixture S))) (and (hot _let_1))))))))
(check-sat-assuming ())
