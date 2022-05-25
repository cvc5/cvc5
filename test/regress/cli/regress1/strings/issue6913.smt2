; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () String)
(assert
 (= (str.++ a "0" (str.at (str.substr (str.++ a a a) 0 3) (str.len a)) "A")
  (str.++ "0" (str.from_code (str.len a)) (str.replace "AA" (str.++ a "AA") a))))
(check-sat)
