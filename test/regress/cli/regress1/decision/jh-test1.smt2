; COMMAND-LINE: --decision=justification --no-strings-code-elim
; EXPECT: sat
(set-logic ALL)
(declare-const size4 String)
(declare-const p2_size Int)
(assert (= 1 (+ 1 (ite (= 1 p2_size) (str.to_code size4) 0))))
(check-sat)
