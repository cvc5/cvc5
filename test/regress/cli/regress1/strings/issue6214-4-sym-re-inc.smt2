; COMMAND-LINE: --strings-exp
; EXPECT: unsat
;; introduces fresh Skolem in a trusted step
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun a () String)
(declare-fun b () String)
(assert
 (str.in_re
  (str.++ (ite (str.in_re b (re.* (re.range "a" "u"))) a "") b)
  (re.++ (re.range "a" "u")
   (re.diff (str.to_re "")
    (str.to_re (ite (str.in_re b (re.* (re.range "a" "u"))) "" b))))))
(assert (str.<= b "a"))
(check-sat)
