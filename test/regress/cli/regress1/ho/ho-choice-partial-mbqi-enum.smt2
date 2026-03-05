; COMMAND-LINE: --mbqi-enum-choice-grammar --sygus-grammar-ho-partial
; EXPECT: unsat
(set-logic HO_ALL)
(declare-sort A 0)
(declare-sort B 0)
(declare-fun r (A B) Bool)
(assert
(and
(exists ((J (-> (-> B Bool) B))) (forall ((P (-> B Bool))) (or (forall ((X B)) (not (P X))) (P (J P)))))
(not (= (forall ((X A)) (exists ((Y B)) (r X Y))) (exists ((F (-> A B))) (forall ((X A)) (r X (F X))))))
))
(set-info :filename SYO268^5)
(check-sat-assuming ( true ))
