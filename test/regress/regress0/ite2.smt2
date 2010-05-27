% EXPECT-ERROR: Outstanding case split in theory arith
% EXPECT-ERROR: Outstanding case split in theory arith
% EXPECT: SAT
% EXIT: 10
(set-logic QF_LRA)
(set-info :status sat)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (not (= x (ite true y x))))
(check-sat)
