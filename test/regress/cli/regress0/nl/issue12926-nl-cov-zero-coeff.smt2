; REQUIRES: poly
; COMMAND-LINE: --nl-ext=none --nl-cov
; EXPECT: sat
(set-logic QF_NRA)
(set-info :status sat)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x () Real)
(declare-fun z () Real)
(assert (= 0 (* x1 x1 x1 x1 x1)))
(assert (= 0 (* x2 x2 x2 x2 x2)))
(assert (= 0 (+ (- (/ 1 3) (* x x x x)) (* x2 z) (* x1 z z z))))
(check-sat)
