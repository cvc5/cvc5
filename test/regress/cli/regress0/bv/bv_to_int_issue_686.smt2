; EXPECT: unsat
; ERROR-SCRUBBER: grep -v "A.proof.step.may.not.hold"
(set-logic ALL)
(set-option :fp-exp true)
(set-option :solve-bv-as-int sum)
(set-option :check-proof-steps true)
(declare-const x Float16)
(assert (fp.isPositive (fp.neg (fp.abs x))))
(check-sat)

