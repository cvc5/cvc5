; COMMAND-LINE: --decision=internal
; EXPECT: sat
(set-logic QF_SLIA)
(declare-fun s () String)
(assert (= "0" (str.substr s (+ 1 1) 1)))
(assert (distinct 1 (str.len (str.substr s (+ 1 1) (+ 1 1)))))
(assert (= 1 (str.len (str.substr s 1 1))))
(assert (= 1 (str.len (str.substr s 0 1))))
(assert (= "0" (str.at (str.substr s (+ 1 1 1) (- (str.len s) (+ 1 1 1))) 0)))
(assert (distinct 1 (str.len (str.substr "00000" (+ 1 1 1) (- (str.len s) (+ 1 1 1))))))
(assert (> (- (str.len s) 1 1 1) 0))
(assert (str.in_re s (re.+ (re.range "0" "9"))))
(assert (<= (- (str.len s) 1 1 (+ 1 1 1)) 0))
(check-sat)
