; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun a () Bool)
(declare-datatypes ((__cvc5_record__a_Int 0)) (((__cvc5_record__a_Int_ctor (_a Int)))))
(define-fun a49 () Bool (= (ite a (__cvc5_record__a_Int_ctor 1) (__cvc5_record__a_Int_ctor 2)) (__cvc5_record__a_Int_ctor (ite a 1 2))))
(check-sat-assuming ( (not (= (ite a (__cvc5_record__a_Int_ctor 1) (__cvc5_record__a_Int_ctor 2)) (__cvc5_record__a_Int_ctor (ite a 1 2)))) ))
