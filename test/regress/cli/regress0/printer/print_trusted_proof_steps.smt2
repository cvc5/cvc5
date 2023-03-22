; COMMAND-LINE: --dump-proofs -o trusted-proof-steps
; SCRUBBER: grep -E '\(trusted-proof-step'
; EXPECT: (trusted-proof-step (=> true (= (= 0 1) false)))
(set-logic ALL)
(assert (= 0 1))
(check-sat)
