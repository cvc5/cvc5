(set-logic ALL)
(set-info :status sat)

(declare-fun a () (Set Int))
(declare-fun b () (Set Int))
(declare-fun c () (Set Int))
(declare-fun d () (Set Int))
(declare-fun e () (Set Int))
(declare-fun f () (Set Int))

(declare-fun x () Int)

(assert (not (member 0 a)))
(assert (member 0 b))
(assert (not (member 1 c)))
(assert (member 2 d))
(assert (= e (as univset (Set Int))))
(assert (= f (complement d)))
(assert (not (member x (as univset (Set Int)))))

(check-sat)
