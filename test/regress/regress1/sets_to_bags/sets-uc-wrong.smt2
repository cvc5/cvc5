; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(set-option :fmf-bound true)
(declare-fun t () (Bag Int))
(declare-fun s () (Bag Int))
(declare-const v Bool)
(assert (forall ((q Bool)) (distinct v (bag.subbag s t))))
(assert (= 1 (bag.card t)))
(check-sat)
(assert v)
(check-sat)
