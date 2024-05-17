; EXPECT: sat
(set-logic ALL)
(declare-const x (_ BitVec 63))
(set-option :lemma-inprocess full)
(assert (fp.isNaN ((_ to_fp 11 53) ((_ zero_extend 1) x))))
(check-sat)
