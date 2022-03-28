; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic QF_SLIA)
(set-info :status sat)
(declare-const x String)
(assert (= (str.len x) 1))
;(assert (= x "X"))
(assert
    (or 
      (not (> (str.len x) 1))
      (= (str.at x 1) "Z")
    )
)
(check-sat)
