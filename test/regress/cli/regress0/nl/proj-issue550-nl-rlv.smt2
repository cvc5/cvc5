; EXPECT: sat
(set-logic QF_NRA)
(set-option :produce-unsat-assumptions true)
(set-option :nl-rlv always)
(declare-const x Real)
(declare-const x1 Real)
(assert (< 0.0 x1))
(check-sat-assuming ((<= 0.0 (/ 0.0 (+ 1.0 x1 x) x1))))
