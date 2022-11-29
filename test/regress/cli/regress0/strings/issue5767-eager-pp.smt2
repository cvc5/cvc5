; COMMAND-LINE: --no-strings-lazy-pp
; EXPECT: sat
(set-logic ALL)
(declare-fun s () String)
(assert (xor (= (str.at s (div 0 0)) "A") (= (div 0 (str.len s)) 0)))
(check-sat)
