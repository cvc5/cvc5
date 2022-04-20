; COMMAND-LINE: -q
; EXPECT: sat
(set-logic QF_UFNIA)
(set-info :status sat)
(set-option :cegqi-all true)
(set-option :miniscope-quant fv)
(set-option :partial-triggers true)
(set-option :full-saturate-quant true)
(set-option :sygus-inference true)
(declare-const i7 Int)
(assert (xor true true true true true (<= (mod 0 (mod i7 5)) 46) true true true true))
(assert (< 775 (mod 0 0)))
(check-sat)
