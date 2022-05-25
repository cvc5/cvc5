; EXPECT: sat
(set-logic ALL)
(set-option :incremental true)
(set-option :produce-models true)
(declare-datatypes ((__cvc5_record_longitude_Int_latitude_Int 0)) (((__cvc5_record_longitude_Int_latitude_Int_ctor (longitude Int) (latitude Int)))))

(declare-datatypes ((|__cvc5_record_geoLoc_(Set __cvc5_record_longitude_Int_latitude_Int)| 0)) (((|__cvc5_record_geoLoc_(Set __cvc5_record_longitude_Int_latitude_Int)_ctor| (geoLoc (Set __cvc5_record_longitude_Int_latitude_Int))))))

(declare-datatypes ((|__cvc5_record_base____cvc5_record_geoLoc_(Set __cvc5_record_longitude_Int_latitude_Int)_| 0)) (((|__cvc5_record_base____cvc5_record_geoLoc_(Set __cvc5_record_longitude_Int_latitude_Int)__ctor| (base |__cvc5_record_geoLoc_(Set __cvc5_record_longitude_Int_latitude_Int)|)))))

(declare-datatypes ((|__cvc5_record_s_f____cvc5_record_base____cvc5_record_geoLoc_(Set __cvc5_record_longitude_Int_latitude_Int)__| 0)) (((|__cvc5_record_s_f____cvc5_record_base____cvc5_record_geoLoc_(Set __cvc5_record_longitude_Int_latitude_Int)___ctor| (s_f |__cvc5_record_base____cvc5_record_geoLoc_(Set __cvc5_record_longitude_Int_latitude_Int)_|)))))


(declare-fun a () (Array Int |__cvc5_record_s_f____cvc5_record_base____cvc5_record_geoLoc_(Set __cvc5_record_longitude_Int_latitude_Int)__|))
(define-fun p1 () __cvc5_record_longitude_Int_latitude_Int (__cvc5_record_longitude_Int_latitude_Int_ctor 0 0))
(define-fun s1 () |__cvc5_record_geoLoc_(Set __cvc5_record_longitude_Int_latitude_Int)| (|__cvc5_record_geoLoc_(Set __cvc5_record_longitude_Int_latitude_Int)_ctor| (set.singleton (__cvc5_record_longitude_Int_latitude_Int_ctor 0 0))))
(define-fun f0 () |__cvc5_record_base____cvc5_record_geoLoc_(Set __cvc5_record_longitude_Int_latitude_Int)_| (|__cvc5_record_base____cvc5_record_geoLoc_(Set __cvc5_record_longitude_Int_latitude_Int)__ctor| (|__cvc5_record_geoLoc_(Set __cvc5_record_longitude_Int_latitude_Int)_ctor| (set.singleton (__cvc5_record_longitude_Int_latitude_Int_ctor 0 0)))))
(define-fun init ((v (Array Int |__cvc5_record_s_f____cvc5_record_base____cvc5_record_geoLoc_(Set __cvc5_record_longitude_Int_latitude_Int)__|)) (i Int) (f |__cvc5_record_base____cvc5_record_geoLoc_(Set __cvc5_record_longitude_Int_latitude_Int)_|)) Bool (= (s_f (select v 0)) f))
(assert (init a 2 (|__cvc5_record_base____cvc5_record_geoLoc_(Set __cvc5_record_longitude_Int_latitude_Int)__ctor| (|__cvc5_record_geoLoc_(Set __cvc5_record_longitude_Int_latitude_Int)_ctor| (set.singleton (__cvc5_record_longitude_Int_latitude_Int_ctor 0 0))))))
(push 1)

(assert true)

(check-sat)

(pop 1)

