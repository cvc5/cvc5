; COMMAND-LINE: --lang=smt2.6.1
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)

(assert (str.is_digit "0"))
(assert (str.is_digit "7"))
(assert (not (str.is_digit "A")))
(assert (not (str.is_digit "")))

(check-sat)
