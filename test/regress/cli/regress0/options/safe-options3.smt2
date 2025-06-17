; COMMAND-LINE: --safe-mode=safe --full-saturate-quant
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic ALL)
(check-sat)
