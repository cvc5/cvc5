; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () (_ BitVec 10))
(check-sat-assuming ( (= x (bvnot x)) ))
