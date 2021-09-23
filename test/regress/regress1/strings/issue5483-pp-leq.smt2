; COMMAND-LINE: -i
; EXPECT: sat
(set-logic QF_SLIA)
(declare-fun _substvar_21_ () String)
(declare-fun _substvar_29_ () String)
(set-option :strings-lazy-pp false)
(assert (xor true true true true (str.<= _substvar_21_ _substvar_29_) true true))
(push 1)
(check-sat)
