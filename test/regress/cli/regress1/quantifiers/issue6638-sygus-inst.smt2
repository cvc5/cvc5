; COMMAND-LINE: --sygus-inst -q
; EXPECT: sat
(set-logic ALL)
(declare-fun b (Int) Int)
(assert (distinct 0 (ite (exists ((t Int)) (and (forall ((tt Int) (t Int)) (! (or (distinct 0 tt) (> 0 (+ tt t)) (> (+ tt t) 0) (= (b 0) (b t))) :qid k!7)))) 1 (b 0))))
(check-sat)

; check-models disabled due to intermediate terms from sygus-inst
