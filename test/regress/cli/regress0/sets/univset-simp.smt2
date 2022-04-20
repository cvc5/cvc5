; COMMAND-LINE: --sets-ext
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)

(declare-fun a () (Set Int))
(declare-fun b () (Set Int))
(declare-fun c () (Set Int))
(declare-fun d () (Set Int))
(declare-fun e () (Set Int))
(declare-fun f () (Set Int))

(declare-fun x () Int)

(assert (not (set.member 0 a)))
(assert (set.member 0 b))
(assert (not (set.member 1 c)))
(assert (set.member 2 d))
(assert (= e (as set.universe (Set Int))))
(assert (= f (set.complement d)))
(assert (not (set.member x (as set.universe (Set Int)))))

(check-sat)
