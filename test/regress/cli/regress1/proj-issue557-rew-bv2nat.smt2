; EXPECT: sat
(set-logic ALL)
(declare-const __ (_ BitVec 1))
(set-option :ext-rew-prep use)
(declare-const x (Seq Bool))
(check-sat-assuming ((<= (bv2nat (_ bv0 80)) (seq.len (seq.extract x (bv2nat (_ bv0 80)) (bv2nat ((_ zero_extend 79) __)))))))
