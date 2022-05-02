; COMMAND-LINE: --fmf-bound
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)

(declare-fun S () (Set Int))
(declare-fun P (Int) Bool)
(declare-fun a () Int)
(assert (set.member a S))
(assert (forall ((y Int)) (=> (set.member y S) (P y))))


(declare-fun T () (Set Int))
(declare-fun b () Int)
(assert (set.member b T))
(assert (forall ((y Int)) (=> (set.member y T) (not (P y)))))

(check-sat)
