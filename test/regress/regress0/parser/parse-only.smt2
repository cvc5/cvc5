; EXIT: 0
; COMMAND-LINE: --parse-only
(set-logic QF_ABV)
(set-option :arrays-exp true)
(declare-fun a1 () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun a2 () (Array (_ BitVec 2) (_ BitVec 2)))
(assert (eqrange a1 a2 #b00 #b01))
(assert (eqrange a1 a2 #b11 #b11))
(check-sat)
