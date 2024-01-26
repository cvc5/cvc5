; COMMAND-LINE: --sygus-inst
; EXPECT: unsat
(set-logic QF_SLIA)
(declare-const x Bool)
(declare-fun T () String)
(declare-fun v () String)
(assert (= (str.++ v v) (str.to_upper (str.to_lower T))))
(assert (= T (str.++ "b" (ite x "_" (str.replace_re_all "c" re.allchar T)))))
(check-sat)

