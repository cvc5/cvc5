; COMMAND-LINE: --model-cores=simple -q
; EXPECT: sat
(set-logic ALL)
(declare-fun a () (Bag String)) 
(assert (= (bag.choose a) "")) 
(check-sat)
