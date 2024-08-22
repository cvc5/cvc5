; DISABLE-TESTER: lfsc
; COMMAND-LINE: --sets-ext --full-saturate-quant
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)

(declare-fun x () (Set Int))

(assert (set.subset (set.comprehension ((z Int)) (>= z 0) (* 3 z)) x))

(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)

(assert (not (set.member a x)))
(assert (not (set.member b x)))
(assert (not (set.member c x)))
(assert (<= 0 a))
(assert (<= a b))
(assert (<= b c))
(assert (< (- c a) 3))
(assert (distinct a b c))

(check-sat)
