; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((|__cvc5_record_b_(_ BitVec 1)| 0)) (((|__cvc5_record_b_(_ BitVec 1)_ctor| (b (_ BitVec 1))))))
(declare-fun x () |__cvc5_record_b_(_ BitVec 1)|)
(assert (= false (= (= x (|__cvc5_record_b_(_ BitVec 1)_ctor| #b0)) (= x (|__cvc5_record_b_(_ BitVec 1)_ctor| #b1)))))
(check-sat)
