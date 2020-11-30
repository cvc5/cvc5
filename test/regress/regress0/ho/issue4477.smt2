; REQUIRES: no-competition
; SCRUBBER: grep -o "Symbol '->' not declared"
; EXPECT: Symbol '->' not declared 
; EXIT: 1
(set-logic ALL)
(declare-sort s 0)
(declare-fun a () s)
(declare-fun b () s)
(declare-fun c (s) s)
(assert (forall ((d (-> s s))) (distinct (d a) (c a) b)))
(check-sat)
