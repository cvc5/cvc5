; COMMAND-LINE: --strings-exp
; EXPECT: unsat
;; introduces RE Skolem
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun str4 () String)
(declare-fun str5 () String)
(assert (str.in_re str4 (re.+ (str.to_re str5))))
(assert (= 1 (str.indexof str5 str4 0)))
(check-sat)
