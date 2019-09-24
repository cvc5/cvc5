; COMMAND-LINE: --sets-ext --full-saturate-quant
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)

(declare-fun x () (Set Int))

(assert (subset (comprehension ((z Int)) (>= z 0) (* 3 z)) x))

(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)

(assert (not (member a x)))
(assert (not (member b x)))
(assert (not (member c x)))
(assert (<= 0 a))
(assert (<= a b))
(assert (<= b c))
(assert (< (- c a) 3))
(assert (distinct a b c))

(check-sat)
