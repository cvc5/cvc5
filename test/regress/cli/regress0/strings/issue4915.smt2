; EXPECT: unsat
; COMMAND-LINE: --strings-exp
(set-logic QF_SLIA)
(declare-const Str4 String)
(declare-const Str18 String)
(assert (str.in_re Str18 (re.++ (str.to_re Str4) (str.to_re "ewgysobutx"))))
(assert (= Str18 (str.++ Str4 "ewgysobutx")))
(assert (>= (str.len (str.substr Str18 0 3)) 937))
(check-sat)
