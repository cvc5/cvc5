; COMMAND-LINE: --print-success
; EXPECT: success
; EXPECT: success
; EXPECT: true
; EXPECT: success
; EXPECT: "done"
; DISABLE-TESTER: dump
(set-logic ALL)
(set-option :produce-proofs true)
(get-option :produce-proofs)
(assert false)
(echo "done")
