; EXPECT: sat
(set-logic ALL)
(declare-const __ (_ BitVec 1))
(set-option :ext-rew-prep use)
(declare-const x (Seq Bool))
(check-sat-assuming ((<= (ubv_to_int (_ bv0 80)) (seq.len (seq.extract x (ubv_to_int (_ bv0 80)) (ubv_to_int ((_ zero_extend 79) __)))))))
