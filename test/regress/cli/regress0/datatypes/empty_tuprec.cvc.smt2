; COMMAND-LINE:
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(set-option :incremental true)
(declare-fun a1 () UnitTuple)
(declare-fun a2 () UnitTuple)
(declare-datatypes ((__cvc5_record 0)) (((__cvc5_record_ctor))))
(declare-fun b1 () __cvc5_record)
(declare-fun b2 () __cvc5_record)
(declare-fun c1 () (Tuple UnitTuple))
(declare-fun c2 () (Tuple UnitTuple))
(declare-datatypes ((__cvc5_record_z_Tuple 0)) (((__cvc5_record_z_Tuple_ctor (z UnitTuple)))))
(declare-datatypes ((|__cvc5_record_x_(Tuple __cvc5_record)_y___cvc5_record_z_Tuple| 0)) (((|__cvc5_record_x_(Tuple __cvc5_record)_y___cvc5_record_z_Tuple_ctor| (x (Tuple __cvc5_record)) (y __cvc5_record_z_Tuple)))))
(declare-fun d1 () |__cvc5_record_x_(Tuple __cvc5_record)_y___cvc5_record_z_Tuple|)
(declare-fun d2 () |__cvc5_record_x_(Tuple __cvc5_record)_y___cvc5_record_z_Tuple|)
(check-sat-assuming ( (not (= a1 a2)) ))
(check-sat-assuming ( (not (= b1 b2)) ))
(check-sat-assuming ( (not (= c1 c2)) ))
(check-sat-assuming ( (not (= d1 d2)) ))
