; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(declare-sort U 0)
(declare-fun c (U U) U)
(declare-fun k () U)
(declare-fun a (U Int) Int)
(assert (or (not (forall ((g U)) (! (or (forall ((x Int)) (! (distinct (a g x) (a k x)) :qid k!10))) :qid k!10))) (exists ((f U) (g U) (x Int)) (distinct (a (c f g) x) (a f (a g x))))))
(check-sat)
(check-sat-assuming ((exists ((f U) (g U) (x Int)) (distinct (a (c f g) x) (a f (a g x))))))
(check-sat-assuming ((exists ((f U) (g U) (x Int)) (distinct (a (c f g) x) (a f (a g x))))))
