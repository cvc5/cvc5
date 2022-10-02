; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(declare-fun a () String)
(assert
 (xor (str.in_re a (re.++ (re.* re.allchar) (str.to_re "A") re.allchar (re.* re.allchar)))
 (str.in_re a (re.++ (re.* (str.to_re a)) (str.to_re "A") re.allchar))))
(check-sat)
