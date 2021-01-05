; EXPECT: unsat

(set-option :strings-exp true)
(set-logic ALL)

(assert (forall ((x (Seq Int)) (xx (Seq Int)) ) (=> (and (= (seq.len x) (seq.len xx)) (forall ((i Int) )   (=> (and (<= 0 i) (< i (seq.len x))) (= (seq.nth x i) (seq.nth xx i))))) (= x xx))))

(declare-fun s@@1 () (Seq Int))
(declare-fun |s'| () (Seq Int))

(assert (not (=> (= (seq.len s@@1) (seq.len |s'|)) (=> (forall ((i@@2 Int) )   (=> (and (<= 0 i@@2) (< i@@2 (seq.len s@@1))) (= (seq.nth s@@1 i@@2) (seq.nth |s'| i@@2)))) (= s@@1 |s'|)))))

(check-sat)
