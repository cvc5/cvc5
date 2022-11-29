; COMMAND-LINE: --strings-exp -i
; EXPECT: sat
(set-logic ALL)
(declare-fun uf6_2 (Bool Bool Bool Bool Bool Bool) Bool)
(declare-fun str2 () String)
(declare-fun str6 () String)
(assert (str.in_re str2 re.allchar))
(assert (str.<= str2 str6))
(check-sat)
(assert (uf6_2 true false true false false (str.<= str2 str6)))
(push)
