; COMMAND-LINE: --solve-int-as-bv=4
; SCRUBBER: grep -o "Cannot translate to BV"
; EXPECT: Cannot translate to BV
; EXIT: 1
(set-logic ALL)
(declare-sort S 0)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun A () (Array S S))
(declare-fun f ((_ BitVec 4)) S)

(assert (distinct (select A (f (_ bv0 4))) (select A (f (_ bv1 4)))))
(check-sat)
