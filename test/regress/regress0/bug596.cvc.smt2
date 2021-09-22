; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((__cvc5_record_i_Int_b_Bool 0)) (((__cvc5_record_i_Int_b_Bool_ctor (i Int) (b Bool)))))
(declare-fun f (Int) __cvc5_record_i_Int_b_Bool)
(declare-fun a () Int)
(assert (not (= (f a) (__cvc5_record_i_Int_b_Bool_ctor 0 false))))
(check-sat)
