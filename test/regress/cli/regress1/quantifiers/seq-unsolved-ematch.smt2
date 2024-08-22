; COMMAND-LINE: --strings-exp --full-saturate-quant
; EXPECT: unsat
(set-logic ALL)

(declare-fun s () (Seq Int))

(declare-fun x () Int)

(assert (and (<= 0 x) (< x (seq.len s))))

(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len s))) (= (seq.nth s i) 0))))

(assert (not (= (seq.nth s x) 0)))

(check-sat)
