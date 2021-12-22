; COMMAND-LINE: --sets-ext --full-saturate-quant
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)

(declare-fun x () (Bag Int))

(assert (bag.subbag (bag.comprehension ((z Int)) (>= z 0) (* 3 z)) x))

(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)

(assert (not (>= (bag.count a x) 1)))
(assert (not (>= (bag.count b x) 1)))
(assert (not (>= (bag.count c x) 1)))
(assert (<= 0 a))
(assert (<= a b))
(assert (<= b c))
(assert (< (- c a) 3))
(assert (distinct a b c))

(check-sat)
