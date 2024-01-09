; COMMAND-LINE: --print-success
; EXPECT: success
; EXPECT: success
; EXPECT: true
; EXPECT: success
; EXPECT: unsat
; EXPECT: "done"
(set-logic ALL)
(set-option :produce-proofs true)
(get-option :produce-proofs)
(assert false)
(check-sat)
(echo "done")
