; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic QF_S)
(set-info :status sat)
(declare-fun x () String)
(assert
 (not
 (str.in_re (str.++ "a" x "ca")
  (re.*
  (re.++ (re.union (str.to_re "a") (str.to_re "b"))
   (re.union (re.* (str.to_re "a")) (str.to_re "b") (str.to_re "c")))))))
(check-sat)
