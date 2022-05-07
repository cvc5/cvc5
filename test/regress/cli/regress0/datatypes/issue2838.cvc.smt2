; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun Ints_0 () (Array Int Int))
(declare-datatypes ((__cvc5_record_i_Int 0)) (((__cvc5_record_i_Int_ctor (i Int)))))


(declare-fun C_0 () (Array Int __cvc5_record_i_Int))
(declare-fun x () Int)
(define-fun C_1 () (Array Int __cvc5_record_i_Int) (store C_0 0 ((_ update i) (select C_0 0) 2)))
(assert (= (i (select C_0 0)) 0))
(assert (= (i (select C_0 1)) 1))
(assert (= (select Ints_0 2) (select Ints_0 0)))
(assert (= x (select Ints_0 (i (select (store C_0 0 ((_ update i) (select C_0 0) 2)) 0)))))
(assert (not (= x (select Ints_0 (i (select (store C_0 0 ((_ update i) (select C_0 0) 2)) 1))))))
(check-sat)
