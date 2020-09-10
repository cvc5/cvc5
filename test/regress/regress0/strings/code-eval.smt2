; COMMAND-LINE: --lang=smt2.6
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)

(assert (< (str.to_code "A") (str.to_code "Z")))
(assert (= (- 1) (str.to_code "AAA")))
(assert (= (- 1) (str.to_code "")))

(check-sat)
