; COMMAND-LINE: --strings-exp --full-saturate-quant
; EXPECT: unsat
(set-logic ALL)

(declare-fun s () (Seq Int))

(declare-fun x () Int)

(declare-fun y () Int)

(assert (and (<= 0 x) (<= x y) (< y (seq.len s))))

(assert (forall ((i Int) (j Int)) (=> (and (<= 0 i) (<= i j) (< j (seq.len s))) (<= (seq.nth s i) (seq.nth s j)))))

(assert (not (<= (seq.nth s x) (seq.nth s y))))

(check-sat)
