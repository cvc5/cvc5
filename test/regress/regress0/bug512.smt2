; COMMAND-LINE: --tlimit-per 2500 -iq
; EXPECT: unknown
; EXPECT: (:reason-unknown incomplete)
; EXPECT: unsat
(set-option :print-success false)
(set-info :smt-lib-version 2.0)
;(set-option :AUTO_CONFIG false)
;(set-option :MODEL_HIDE_UNUSED_PARTITIONS false)
;(set-option :MODEL_V2 true)
;(set-option :ASYNC_COMMANDS false)
;(set-option :PHASE_SELECTION 0)
;(set-option :RESTART_STRATEGY 0)
;(set-option :RESTART_FACTOR |1.5|)
;(set-option :ARITH_RANDOM_INITIAL_VALUE true)
;(set-option :CASE_SPLIT 3)
;(set-option :DELAY_UNITS true)
;(set-option :DELAY_UNITS_THRESHOLD 16)
;(set-option :NNF_SK_HACK true)
;(set-option :MBQI false)
;(set-option :QI_EAGER_THRESHOLD 100)
;(set-option :QI_COST |"(+ weight generation)"|)
;(set-option :TYPE_CHECK true)
;(set-option :BV_REFLECT true)
; done setting options

; Boogie universal background predicate
; Copyright (c) 2004-2010, Microsoft Corp.
(set-info :category "industrial")
(declare-sort |T@U| 0)
(declare-sort |T@T| 0)
(declare-fun real_pow (Real Real) Real)
(declare-fun UOrdering2 (|T@U| |T@U|) Bool)
(declare-fun UOrdering3 (|T@T| |T@U| |T@U|) Bool)

(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-fun Ctor (T@T) Int)
(declare-fun intType () T@T)
(declare-fun realType () T@T)
(declare-fun boolType () T@T)
(declare-fun int_2_U (Int) T@U)
(declare-fun U_2_int (T@U) Int)
(declare-fun type (T@U) T@T)
(declare-fun real_2_U (Real) T@U)
(declare-fun U_2_real (T@U) Real)
(declare-fun bool_2_U (Bool) T@U)
(declare-fun U_2_bool (T@U) Bool)
(declare-fun %lbl%+67 () Bool)
(declare-fun i@0 () Int)
(declare-fun x@@5 () Int)
(declare-fun y@@1 () Int)
(declare-fun i@1 () Int)
(declare-fun %lbl%@186 () Bool)
(declare-fun %lbl%+69 () Bool)
(declare-fun %lbl%@157 () Bool)
(declare-fun %lbl%+65 () Bool)
(declare-fun %lbl%+63 () Bool)
(declare-fun %lbl%@125 () Bool)
(declare-fun %lbl%+97 () Bool)
(assert (and
(= (Ctor intType) 0)
(= (Ctor realType) 1)
(= (Ctor boolType) 2)
(forall ((arg0 Int) ) (! (= (U_2_int (int_2_U arg0)) arg0)
 :qid |typeInv:U_2_int|
 :pattern ( (int_2_U arg0))
))
(forall ((x T@U) ) (! (=> (= (type x) intType) (= (int_2_U (U_2_int x)) x))
 :qid |cast:U_2_int|
 :pattern ( (U_2_int x))
))
(forall ((arg0@@0 Int) ) (! (= (type (int_2_U arg0@@0)) intType)
 :qid |funType:int_2_U|
 :pattern ( (int_2_U arg0@@0))
))
(forall ((arg0@@1 Real) ) (! (= (U_2_real (real_2_U arg0@@1)) arg0@@1)
 :qid |typeInv:U_2_real|
 :pattern ( (real_2_U arg0@@1))
))
(forall ((x@@0 T@U) ) (! (=> (= (type x@@0) realType) (= (real_2_U (U_2_real x@@0)) x@@0))
 :qid |cast:U_2_real|
 :pattern ( (U_2_real x@@0))
))
(forall ((arg0@@2 Real) ) (! (= (type (real_2_U arg0@@2)) realType)
 :qid |funType:real_2_U|
 :pattern ( (real_2_U arg0@@2))
))
(forall ((arg0@@3 Bool) ) (! (= (U_2_bool (bool_2_U arg0@@3)) arg0@@3)
 :qid |typeInv:U_2_bool|
 :pattern ( (bool_2_U arg0@@3))
))
(forall ((x@@1 T@U) ) (! (=> (= (type x@@1) boolType) (= (bool_2_U (U_2_bool x@@1)) x@@1))
 :qid |cast:U_2_bool|
 :pattern ( (U_2_bool x@@1))
))
(forall ((arg0@@4 Bool) ) (! (= (type (bool_2_U arg0@@4)) boolType)
 :qid |funType:bool_2_U|
 :pattern ( (bool_2_U arg0@@4))
))))
(assert (forall ((x@@2 T@U) ) (! (UOrdering2 x@@2 x@@2)
 :qid |bg:subtype-refl|
 :no-pattern (U_2_int x@@2)
 :no-pattern (U_2_bool x@@2)
)))
(assert (forall ((x@@3 T@U) (y T@U) (z T@U) ) (! (let ((alpha (type x@@3)))
(=> (and
(= (type y) alpha)
(= (type z) alpha)
(UOrdering2 x@@3 y)
(UOrdering2 y z)) (UOrdering2 x@@3 z)))
 :qid |bg:subtype-trans|
 :pattern ( (UOrdering2 x@@3 y) (UOrdering2 y z))
)))
(assert (forall ((x@@4 T@U) (y@@0 T@U) ) (! (let ((alpha@@0 (type x@@4)))
(=> (= (type y@@0) alpha@@0) (=> (and
(UOrdering2 x@@4 y@@0)
(UOrdering2 y@@0 x@@4)) (= x@@4 y@@0))))
 :qid |bg:subtype-antisymm|
 :pattern ( (UOrdering2 x@@4 y@@0) (UOrdering2 y@@0 x@@4))
)))
(push 1)
(set-info :boogie-vc-id foo)
(assert (not
(let ((anon3_LoopBody_correct (=> (! (and %lbl%+67 true) :lblpos +67) (=> (and
(< i@0 (+ x@@5 y@@1))
(= i@1 (+ i@0 1))) (and
(! (or %lbl%@186 (<= i@1 (+ x@@5 y@@1))) :lblneg @186)
(=> (<= i@1 (+ x@@5 y@@1)) true))))))
(let ((anon3_LoopDone_correct (=> (! (and %lbl%+69 true) :lblpos +69) (=> (<= (+ x@@5 y@@1) i@0) (and
(! (or %lbl%@157 (= i@0 (- x@@5 y@@1))) :lblneg @157)
(=> (= i@0 (- x@@5 y@@1)) true))))))
(let ((anon3_LoopHead_correct (=> (! (and %lbl%+65 true) :lblpos +65) (=> (<= i@0 (+ x@@5 y@@1)) (and
anon3_LoopDone_correct
anon3_LoopBody_correct)))))
(let ((anon0_correct (=> (! (and %lbl%+63 true) :lblpos +63) (and
(! (or %lbl%@125 (<= x@@5 (+ x@@5 y@@1))) :lblneg @125)
(=> (<= x@@5 (+ x@@5 y@@1)) anon3_LoopHead_correct)))))
(let ((PreconditionGeneratedEntry_correct (=> (! (and %lbl%+97 true) :lblpos +97) (=> (>= y@@1 0) anon0_correct))))
PreconditionGeneratedEntry_correct)))))
))
(check-sat)
(get-info :reason-unknown)
;(labels)
(assert %lbl%@157)
(check-sat)
(pop 1)
