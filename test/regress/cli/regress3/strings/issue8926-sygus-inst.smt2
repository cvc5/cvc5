; COMMAND-LINE: --sygus-inst
; EXPECT: sat
(set-logic QF_SLIA)
(declare-fun tstr () String)
(assert (ite (str.prefixof "-" (str.substr tstr 0 (- (+ 0 2) 0))) (and (ite (= (- 1) (str.to_int (str.substr (str.substr tstr 0 (- (+ 0 2) 0)) 1 (- (str.len (str.substr tstr 0 (- (+ 0 2) 0))) 1)))) false true) (> (str.len (str.substr tstr 0 (- (+ 0 2) 0))) 1)) (ite (= (- 1) (str.to_int (str.substr tstr 0 (- (+ 0 2) 0)))) false true)))
(assert (not (< (str.len tstr) (str.to_code (str.rev tstr)))))
(assert (>= 3 (str.len tstr)))
(check-sat)
