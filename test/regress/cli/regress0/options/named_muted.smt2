; DISABLE-TESTER: dump
; COMMAND-LINE: --print-success
; EXPECT: success
; EXPECT: success

(set-logic UF)
(assert (! true :named t))
