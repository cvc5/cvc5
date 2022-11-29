; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
(check-sat-assuming ( (not (= (pred zero) zero)) ))
