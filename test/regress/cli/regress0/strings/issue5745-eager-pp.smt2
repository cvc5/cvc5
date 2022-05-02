; COMMAND-LINE: --no-strings-lazy-pp
; EXPECT: sat
(set-logic ALL)
(declare-fun i0 () Int)
(declare-fun str4 () String)
(assert (= str4 (str.substr str4 (mod i0 2) 1)))
(assert (not (= "" str4)))
(check-sat)
