; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
(declare-fun x () nat)
(check-sat-assuming ( (not (and (not ((_ is succ) x)) (not ((_ is zero) x)))) ))
