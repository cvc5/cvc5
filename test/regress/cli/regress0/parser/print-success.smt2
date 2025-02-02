; COMMAND-LINE: --print-success
; EXPECT: success
; EXPECT: success
; EXPECT: true
; EXPECT: success
; EXPECT: "done"
; DISABLE-TESTER: dump
(set-logic ALL)
(set-option :produce-models true)
(get-option :produce-models)
(assert false)
(echo "done")
