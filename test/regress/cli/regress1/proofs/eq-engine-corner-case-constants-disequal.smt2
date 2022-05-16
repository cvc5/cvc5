; COMMAND-LINE: --produce-proofs
; EXPECT: sat
(set-logic QF_SLIA)
(declare-const x Bool)
(declare-fun s () String)
(assert (ite (str.prefixof "-" (str.substr s 1 1)) true x))
(assert (> (- (str.len s) 1 (+ 1 1) (+ 1 1)) 0))
(assert (str.in_re s (re.+ (re.range "0" "9"))))
(assert (= 1 (str.to_int (str.substr s (+ 1 1 1 1) (+ 1 1)))))
(check-sat)
