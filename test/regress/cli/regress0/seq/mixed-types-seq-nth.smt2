; COMMAND-LINE: --seq-array=lazy

(set-logic QF_UFSLIA)
(declare-sort E 0)
(declare-const s1 (Seq Int))
(declare-const s2 (Seq Int))
(declare-const s3 (Seq E))
(declare-const s4 (Seq E))

(declare-const i Int)

(assert (distinct (seq.nth s1 i) (seq.nth s2 i)))
(assert (distinct (seq.nth s3 i) (seq.nth s4 i)))

(set-info :status sat)
(check-sat)
