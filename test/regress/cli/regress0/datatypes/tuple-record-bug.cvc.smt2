; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)

(declare-datatypes ((|__cvc5_record_int_(Array Int Int)_queries_(Array Int Int)| 0)) (((|__cvc5_record_int_(Array Int Int)_queries_(Array Int Int)_ctor| (int (Array Int Int)) (queries (Array Int Int))))))

(declare-fun x () Int)
(define-fun foo ((x |__cvc5_record_int_(Array Int Int)_queries_(Array Int Int)|)) |__cvc5_record_int_(Array Int Int)_queries_(Array Int Int)| ((_ update int) x (int x)))
(declare-fun m () |__cvc5_record_int_(Array Int Int)_queries_(Array Int Int)|)
(define-fun w () (Tuple |__cvc5_record_int_(Array Int Int)_queries_(Array Int Int)| Int) (ite (= x 0) (tuple (foo m) 0) (tuple m 0)))
(check-sat-assuming ( (not (= ((_ tuple.select 1) (ite (= x 0) (tuple (foo m) 0) (tuple m 0))) 1)) ))
