; COMMAND-LINE: --incremental --strings-exp
; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status sat)

(declare-fun u () String)
(declare-fun s () String)

(assert (= (str.len u) 9))
(assert (= (str.at u 1) s))
(assert (= (str.at u 2) "4"))
(assert (= (str.at u 7) "5"))
(assert (= (str.at u 8) "6"))

(push 1)
(assert (str.in_re s (re.range "0" "3")))

(check-sat)
