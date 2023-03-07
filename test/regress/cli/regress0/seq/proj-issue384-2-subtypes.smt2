; EXPECT: sat
(set-logic QF_ALL)
(set-info :status sat)
(declare-const x Real)
(check-sat-assuming ((= 0.0 (/ 0.0 x)) (seq.contains (seq.unit x) (seq.rev (seq.unit x)))))
