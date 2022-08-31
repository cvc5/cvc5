; COMMAND-LINE: -o sat-lemmas
; SCRUBBER: grep -E '\(assert'
; EXPECT: (sat-lemma (=> (forall ((x Int)) (P x)) (P 5)))
(set-logic ALL)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (P x)))
(assert (not (P 5)))
(check-sat)
