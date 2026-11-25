; COMMAND-LINE: --strings-alpha-card=1114112
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
(set-logic QF_SLIA)
(set-option :incremental true)
(declare-fun x () String)
; code points outside of the SMT-LIB alphabet are in the alphabet
(push 1)
(assert (= (str.len x) 1))
(assert (> (str.to_code x) 196607))
(check-sat)
(pop 1)
; escape sequences with 5 and 6 digits denote single characters
(push 1)
(assert (= x "\u{30000}\u{10FFFF}"))
(assert (not (= (str.len x) 2)))
(check-sat)
(pop 1)
; the maximum code point, also as an indexed character
(push 1)
(assert (= x (_ char #x10FFFF)))
(assert (not (and (= x "\u{10FFFF}") (= (str.to_code x) 1114111))))
(check-sat)
(pop 1)
; escape sequences beyond the maximum code point are taken verbatim
(push 1)
(assert (= x "\u{110000}"))
(assert (not (= (str.len x) 10)))
(check-sat)
(pop 1)
