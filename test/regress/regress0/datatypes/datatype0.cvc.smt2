; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
(declare-fun x () nat)
(check-sat-assuming ( (not (or ((_ is succ) x) ((_ is zero) x))) ))
