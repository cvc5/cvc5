; COMMAND-LINE: -o lemmas
; SCRUBBER: grep -E '\(lemma'
; EXPECT: (lemma (=> (forall ((x Int)) (P x)) (P 5)) :source QUANTIFIERS_INST_CBQI_CONFLICT)
(set-logic ALL)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (P x)))
(assert (not (P 5)))
(check-sat)
