; COMMAND-LINE: --no-strings-lazy-pp
; EXPECT: sat
(set-logic QF_SLIA)
(declare-fun s () String)
(assert (> (- (str.len s) (+ 1 1) 1 1) 0))
(assert (= "0" (str.substr s (+ 1 1 1 1) 1)))
(assert (> (- (str.len s) (str.len (str.update (str.++ "9" "0") (str.to_int "0") s)) (+ 1 1) (+ (+ 1 1) 1)) 0))
(check-sat)
