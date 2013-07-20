;(set-option :produce-unsat-cores true)
(set-option :incremental true)
(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-info :status sat)
(set-option :produce-models true)
(set-logic ALL_SUPPORTED)
; done setting options

; Boogie universal background predicate
; Copyright (c) 2004-2010, Microsoft Corp.
(set-info :category "industrial")
(declare-sort |T@U| 0)
(declare-sort |T@T| 0)
(declare-fun real_pow (Real Real) Real)
(declare-fun UOrdering2 (|T@U| |T@U|) Bool)
(declare-fun UOrdering3 (|T@T| |T@U| |T@U|) Bool)

(declare-fun group_size_y () (_ BitVec 32))
(declare-fun group_size_z () (_ BitVec 32))
(declare-fun num_groups_y () (_ BitVec 32))
(declare-fun num_groups_z () (_ BitVec 32))
(declare-fun group_size_x () (_ BitVec 32))
(declare-fun num_groups_x () (_ BitVec 32))
(declare-fun ControlFlow (Int Int) Int)
(declare-fun %lbl%+1458 () Bool)
(declare-fun %lbl%@3203 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$p$1@2 () Bool)
(declare-fun _WRITE_SOURCE_$$p$1@2 () (_ BitVec 32))
(declare-fun %lbl%@3213 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$p$1 () Bool)
(declare-fun _READ_SOURCE_$$p$1 () (_ BitVec 32))
(declare-fun %lbl%@3225 () Bool)
(declare-fun %lbl%@3240 () Bool)
(declare-fun %lbl%+1440 () Bool)
(declare-fun $mv_state (Int Int) Bool)
(declare-fun $mv_state_const () Int)
(declare-fun call465formal@_offset$2@0 () (_ BitVec 32))
(declare-fun group_id_x$2 () (_ BitVec 32))
(declare-fun local_id_x$2 () (_ BitVec 32))
(declare-fun call465formal@_value$2@0 () (_ BitVec 32))
(declare-fun %lbl%@3060 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$p$1@1 () Bool)
(declare-fun _WRITE_OFFSET_$$p$1@1 () (_ BitVec 32))
(declare-fun _WRITE_VALUE_$$p$1@1 () (_ BitVec 32))
(declare-fun %lbl%@3078 () Bool)
(declare-fun _READ_OFFSET_$$p$1 () (_ BitVec 32))
(declare-fun _READ_VALUE_$$p$1 () (_ BitVec 32))
(declare-fun %lbl%@3099 () Bool)
(declare-fun _WRITE_SOURCE_$$p$1@1 () (_ BitVec 32))
(declare-fun %lbl%@3109 () Bool)
(declare-fun %lbl%@3121 () Bool)
(declare-fun %lbl%@3136 () Bool)
(declare-fun %lbl%+1434 () Bool)
(declare-fun inline$_LOG_WRITE_$$p$1$track@1 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$p$1@0 () Bool)
(declare-fun inline$_LOG_WRITE_$$p$1$_offset$1@0 () (_ BitVec 32))
(declare-fun _WRITE_OFFSET_$$p$1@0 () (_ BitVec 32))
(declare-fun inline$_LOG_WRITE_$$p$1$_value$1@0 () (_ BitVec 32))
(declare-fun _WRITE_VALUE_$$p$1@0 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$p$1@0 () (_ BitVec 32))
(declare-fun %lbl%+1432 () Bool)
(declare-fun group_id_x$1 () (_ BitVec 32))
(declare-fun local_id_x$1 () (_ BitVec 32))
(declare-fun %lbl%+1328 () Bool)
(declare-fun group_id_y$1 () (_ BitVec 32))
(declare-fun group_id_y$2 () (_ BitVec 32))
(declare-fun group_id_z$1 () (_ BitVec 32))
(declare-fun group_id_z$2 () (_ BitVec 32))
(declare-fun %lbl%+1330 () Bool)
(declare-fun %lbl%+1324 () Bool)
(declare-fun %lbl%@2798 () Bool)
(declare-fun %lbl%+1334 () Bool)
(declare-fun call397formal@_offset$2@0 () (_ BitVec 32))
(declare-fun call397formal@_value$2@0 () (_ BitVec 32))
(declare-fun %lbl%@2667 () Bool)
(declare-fun %lbl%@2685 () Bool)
(declare-fun %lbl%@2706 () Bool)
(declare-fun %lbl%@2716 () Bool)
(declare-fun %lbl%@2728 () Bool)
(declare-fun %lbl%@2743 () Bool)
(declare-fun %lbl%+1189 () Bool)
(declare-fun inline$_LOG_WRITE_$$p$0$track@1 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$p$1 () Bool)
(declare-fun inline$_LOG_WRITE_$$p$0$_offset$1@0 () (_ BitVec 32))
(declare-fun _WRITE_OFFSET_$$p$1 () (_ BitVec 32))
(declare-fun inline$_LOG_WRITE_$$p$0$_value$1@0 () (_ BitVec 32))
(declare-fun _WRITE_VALUE_$$p$1 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$p$1 () (_ BitVec 32))
(declare-fun %lbl%+1187 () Bool)
(declare-fun %lbl%+1462 () Bool)
(declare-fun local_id_y$1 () (_ BitVec 32))
(declare-fun local_id_y$2 () (_ BitVec 32))
(declare-fun local_id_z$1 () (_ BitVec 32))
(declare-fun local_id_z$2 () (_ BitVec 32))
(assert (not (= (ite (= group_size_y #x00000001) #b1 #b0) #b0)))
(assert (not (= (ite (= group_size_z #x00000001) #b1 #b0) #b0)))
(assert (not (= (ite (= num_groups_y #x00000001) #b1 #b0) #b0)))
(assert (not (= (ite (= num_groups_z #x00000001) #b1 #b0) #b0)))
(assert (not (= (ite (= group_size_x #x00000400) #b1 #b0) #b0)))
(assert (not (= (ite (= num_groups_x #x00000400) #b1 #b0) #b0)))
(define-fun $foo () Bool (=> (= (ControlFlow 0 0) 1462) (let ((GeneratedUnifiedExit_correct (=> (and %lbl%+1458 true) (and
(or %lbl%@3203 (=> (= (ControlFlow 0 1458) (- 0 3203)) (=> (not _WRITE_HAS_OCCURRED_$$p$1@2) (= _WRITE_SOURCE_$$p$1@2 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$p$1@2) (= _WRITE_SOURCE_$$p$1@2 #x00000000)) (and
(or %lbl%@3213 (=> (= (ControlFlow 0 1458) (- 0 3213)) (=> (not _READ_HAS_OCCURRED_$$p$1) (= _READ_SOURCE_$$p$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$p$1) (= _READ_SOURCE_$$p$1 #x00000000)) (and
(or %lbl%@3225 (=> (= (ControlFlow 0 1458) (- 0 3225)) (=> _WRITE_HAS_OCCURRED_$$p$1@2 (or
(= _WRITE_SOURCE_$$p$1@2 #x00000001)
(= _WRITE_SOURCE_$$p$1@2 #x00000002)))))
(=> (=> _WRITE_HAS_OCCURRED_$$p$1@2 (or
(= _WRITE_SOURCE_$$p$1@2 #x00000001)
(= _WRITE_SOURCE_$$p$1@2 #x00000002))) (and
(or %lbl%@3240 (=> (= (ControlFlow 0 1458) (- 0 3240)) (=> _READ_HAS_OCCURRED_$$p$1 false)))
(=> (=> _READ_HAS_OCCURRED_$$p$1 false) true)))))))))))
(let (($0$3_correct (=> (and %lbl%+1440 true) (=> (and
($mv_state $mv_state_const 1)
true
(= call465formal@_offset$2@0 (bvadd (bvadd (bvmul group_size_x group_id_x$2) local_id_x$2) #x00000001))
(= call465formal@_value$2@0 (bvadd (bvmul group_size_x group_id_x$2) local_id_x$2))) (and
(or %lbl%@3060 (=> (= (ControlFlow 0 1440) (- 0 3060)) (not (and
true
_WRITE_HAS_OCCURRED_$$p$1@1
(= _WRITE_OFFSET_$$p$1@1 call465formal@_offset$2@0)
(not (= _WRITE_VALUE_$$p$1@1 call465formal@_value$2@0))))))
(=> (not (and
true
_WRITE_HAS_OCCURRED_$$p$1@1
(= _WRITE_OFFSET_$$p$1@1 call465formal@_offset$2@0)
(not (= _WRITE_VALUE_$$p$1@1 call465formal@_value$2@0)))) (and
(or %lbl%@3078 (=> (= (ControlFlow 0 1440) (- 0 3078)) (not (and
true
_READ_HAS_OCCURRED_$$p$1
(= _READ_OFFSET_$$p$1 call465formal@_offset$2@0)
(not (= _READ_VALUE_$$p$1 call465formal@_value$2@0))))))
(=> (not (and
true
_READ_HAS_OCCURRED_$$p$1
(= _READ_OFFSET_$$p$1 call465formal@_offset$2@0)
(not (= _READ_VALUE_$$p$1 call465formal@_value$2@0)))) (and
(or %lbl%@3099 (=> (= (ControlFlow 0 1440) (- 0 3099)) (=> (not _WRITE_HAS_OCCURRED_$$p$1@1) (= _WRITE_SOURCE_$$p$1@1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$p$1@1) (= _WRITE_SOURCE_$$p$1@1 #x00000000)) (and
(or %lbl%@3109 (=> (= (ControlFlow 0 1440) (- 0 3109)) (=> (not _READ_HAS_OCCURRED_$$p$1) (= _READ_SOURCE_$$p$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$p$1) (= _READ_SOURCE_$$p$1 #x00000000)) (and
(or %lbl%@3121 (=> (= (ControlFlow 0 1440) (- 0 3121)) (=> _WRITE_HAS_OCCURRED_$$p$1@1 (or
(= _WRITE_SOURCE_$$p$1@1 #x00000001)
(= _WRITE_SOURCE_$$p$1@1 #x00000002)))))
(=> (=> _WRITE_HAS_OCCURRED_$$p$1@1 (or
(= _WRITE_SOURCE_$$p$1@1 #x00000001)
(= _WRITE_SOURCE_$$p$1@1 #x00000002))) (and
(or %lbl%@3136 (=> (= (ControlFlow 0 1440) (- 0 3136)) (=> _READ_HAS_OCCURRED_$$p$1 false)))
(=> (=> _READ_HAS_OCCURRED_$$p$1 false) (=> (=> (not _WRITE_HAS_OCCURRED_$$p$1@1) (= _WRITE_SOURCE_$$p$1@1 #x00000000)) (=> (and
(=> (not _READ_HAS_OCCURRED_$$p$1) (= _READ_SOURCE_$$p$1 #x00000000))
(=> _WRITE_HAS_OCCURRED_$$p$1@1 (or
(= _WRITE_SOURCE_$$p$1@1 #x00000001)
(= _WRITE_SOURCE_$$p$1@1 #x00000002)))) (=> (and
(=> _READ_HAS_OCCURRED_$$p$1 false)
(= _WRITE_HAS_OCCURRED_$$p$1@2 _WRITE_HAS_OCCURRED_$$p$1@1)
(= _WRITE_SOURCE_$$p$1@2 _WRITE_SOURCE_$$p$1@1)
(= (ControlFlow 0 1440) 1458)) GeneratedUnifiedExit_correct)))))))))))))))))))
(let ((inline$_LOG_WRITE_$$p$1$_LOG_WRITE_correct (=> (and %lbl%+1434 true) (=> (= _WRITE_HAS_OCCURRED_$$p$1@1 (ite (and
true
inline$_LOG_WRITE_$$p$1$track@1) true _WRITE_HAS_OCCURRED_$$p$1@0)) (=> (and
(= _WRITE_OFFSET_$$p$1@1 (ite (and
true
inline$_LOG_WRITE_$$p$1$track@1) inline$_LOG_WRITE_$$p$1$_offset$1@0 _WRITE_OFFSET_$$p$1@0))
(= _WRITE_VALUE_$$p$1@1 (ite (and
true
inline$_LOG_WRITE_$$p$1$track@1) inline$_LOG_WRITE_$$p$1$_value$1@0 _WRITE_VALUE_$$p$1@0))
(= _WRITE_SOURCE_$$p$1@1 (ite (and
true
inline$_LOG_WRITE_$$p$1$track@1) #x00000002 _WRITE_SOURCE_$$p$1@0))
(= (ControlFlow 0 1434) 1440)) $0$3_correct)))))
(let ((inline$_LOG_WRITE_$$p$1$Entry_correct (=> (and %lbl%+1432 true) (=> (= inline$_LOG_WRITE_$$p$1$_offset$1@0 (bvadd (bvadd (bvmul group_size_x group_id_x$1) local_id_x$1) #x00000001)) (=> (and
(= inline$_LOG_WRITE_$$p$1$_value$1@0 (bvadd (bvmul group_size_x group_id_x$1) local_id_x$1))
(= (ControlFlow 0 1432) 1434)) inline$_LOG_WRITE_$$p$1$_LOG_WRITE_correct)))))
(let ((inline$$bugle_barrier$0$anon1_Else_correct (=> (and %lbl%+1328 true) (=> (=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (=> (= #b1 #b1) (not _READ_HAS_OCCURRED_$$p$1))) (=> (and
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (=> (= #b1 #b1) (not _WRITE_HAS_OCCURRED_$$p$1@0)))
(= (ControlFlow 0 1328) 1432)) inline$_LOG_WRITE_$$p$1$Entry_correct)))))
(let ((inline$$bugle_barrier$0$anon1_Then_correct (=> (and %lbl%+1330 true) true)))
(let ((inline$$bugle_barrier$0$Entry_correct (=> (and %lbl%+1324 true) (and
(or %lbl%@2798 (=> (= (ControlFlow 0 1324) (- 0 2798)) (=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (= true true))))
(=> (=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (= true true)) (and
(=> (= (ControlFlow 0 1324) 1330) inline$$bugle_barrier$0$anon1_Then_correct)
(=> (= (ControlFlow 0 1324) 1328) inline$$bugle_barrier$0$anon1_Else_correct)))))))
(let (($0$1_correct (=> (and %lbl%+1334 true) (=> (and
($mv_state $mv_state_const 0)
true
(= call397formal@_offset$2@0 (bvadd (bvmul group_size_x group_id_x$2) local_id_x$2))
(= call397formal@_value$2@0 (bvadd (bvmul group_size_x group_id_x$2) local_id_x$2))) (and
(or %lbl%@2667 (=> (= (ControlFlow 0 1334) (- 0 2667)) (not (and
true
_WRITE_HAS_OCCURRED_$$p$1@0
(= _WRITE_OFFSET_$$p$1@0 call397formal@_offset$2@0)
(not (= _WRITE_VALUE_$$p$1@0 call397formal@_value$2@0))))))
(=> (not (and
true
_WRITE_HAS_OCCURRED_$$p$1@0
(= _WRITE_OFFSET_$$p$1@0 call397formal@_offset$2@0)
(not (= _WRITE_VALUE_$$p$1@0 call397formal@_value$2@0)))) (and
(or %lbl%@2685 (=> (= (ControlFlow 0 1334) (- 0 2685)) (not (and
true
_READ_HAS_OCCURRED_$$p$1
(= _READ_OFFSET_$$p$1 call397formal@_offset$2@0)
(not (= _READ_VALUE_$$p$1 call397formal@_value$2@0))))))
(=> (not (and
true
_READ_HAS_OCCURRED_$$p$1
(= _READ_OFFSET_$$p$1 call397formal@_offset$2@0)
(not (= _READ_VALUE_$$p$1 call397formal@_value$2@0)))) (and
(or %lbl%@2706 (=> (= (ControlFlow 0 1334) (- 0 2706)) (=> (not _WRITE_HAS_OCCURRED_$$p$1@0) (= _WRITE_SOURCE_$$p$1@0 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$p$1@0) (= _WRITE_SOURCE_$$p$1@0 #x00000000)) (and
(or %lbl%@2716 (=> (= (ControlFlow 0 1334) (- 0 2716)) (=> (not _READ_HAS_OCCURRED_$$p$1) (= _READ_SOURCE_$$p$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$p$1) (= _READ_SOURCE_$$p$1 #x00000000)) (and
(or %lbl%@2728 (=> (= (ControlFlow 0 1334) (- 0 2728)) (=> _WRITE_HAS_OCCURRED_$$p$1@0 (or
(= _WRITE_SOURCE_$$p$1@0 #x00000001)
(= _WRITE_SOURCE_$$p$1@0 #x00000002)))))
(=> (=> _WRITE_HAS_OCCURRED_$$p$1@0 (or
(= _WRITE_SOURCE_$$p$1@0 #x00000001)
(= _WRITE_SOURCE_$$p$1@0 #x00000002))) (and
(or %lbl%@2743 (=> (= (ControlFlow 0 1334) (- 0 2743)) (=> _READ_HAS_OCCURRED_$$p$1 false)))
(=> (=> _READ_HAS_OCCURRED_$$p$1 false) (=> (=> (not _WRITE_HAS_OCCURRED_$$p$1@0) (= _WRITE_SOURCE_$$p$1@0 #x00000000)) (=> (and
(=> (not _READ_HAS_OCCURRED_$$p$1) (= _READ_SOURCE_$$p$1 #x00000000))
(=> _WRITE_HAS_OCCURRED_$$p$1@0 (or
(= _WRITE_SOURCE_$$p$1@0 #x00000001)
(= _WRITE_SOURCE_$$p$1@0 #x00000002)))
(=> _READ_HAS_OCCURRED_$$p$1 false)
(= (ControlFlow 0 1334) 1324)) inline$$bugle_barrier$0$Entry_correct))))))))))))))))))
(let ((inline$_LOG_WRITE_$$p$0$_LOG_WRITE_correct (=> (and %lbl%+1189 true) (=> (= _WRITE_HAS_OCCURRED_$$p$1@0 (ite (and
true
inline$_LOG_WRITE_$$p$0$track@1) true _WRITE_HAS_OCCURRED_$$p$1)) (=> (and
(= _WRITE_OFFSET_$$p$1@0 (ite (and
true
inline$_LOG_WRITE_$$p$0$track@1) inline$_LOG_WRITE_$$p$0$_offset$1@0 _WRITE_OFFSET_$$p$1))
(= _WRITE_VALUE_$$p$1@0 (ite (and
true
inline$_LOG_WRITE_$$p$0$track@1) inline$_LOG_WRITE_$$p$0$_value$1@0 _WRITE_VALUE_$$p$1))
(= _WRITE_SOURCE_$$p$1@0 (ite (and
true
inline$_LOG_WRITE_$$p$0$track@1) #x00000001 _WRITE_SOURCE_$$p$1))
(= (ControlFlow 0 1189) 1334)) $0$1_correct)))))
(let ((inline$_LOG_WRITE_$$p$0$Entry_correct (=> (and %lbl%+1187 true) (=> (= inline$_LOG_WRITE_$$p$0$_offset$1@0 (bvadd (bvmul group_size_x group_id_x$1) local_id_x$1)) (=> (and
(= inline$_LOG_WRITE_$$p$0$_value$1@0 (bvadd (bvmul group_size_x group_id_x$1) local_id_x$1))
(= (ControlFlow 0 1187) 1189)) inline$_LOG_WRITE_$$p$0$_LOG_WRITE_correct)))))
(let (($0_correct (=> (and %lbl%+1462 true) (=> (and
(not _READ_HAS_OCCURRED_$$p$1)
(not _WRITE_HAS_OCCURRED_$$p$1)
(= _READ_SOURCE_$$p$1 #x00000000)
(= _WRITE_SOURCE_$$p$1 #x00000000)
(bvsgt group_size_x #x00000000)
(bvsgt num_groups_x #x00000000)
(bvsge group_id_x$1 #x00000000)
(bvsge group_id_x$2 #x00000000)) (=> (and
(bvslt group_id_x$1 num_groups_x)
(bvslt group_id_x$2 num_groups_x)
(bvsge local_id_x$1 #x00000000)
(bvsge local_id_x$2 #x00000000)
(bvslt local_id_x$1 group_size_x)
(bvslt local_id_x$2 group_size_x)
(bvsgt group_size_y #x00000000)
(bvsgt num_groups_y #x00000000)
(bvsge group_id_y$1 #x00000000)
(bvsge group_id_y$2 #x00000000)
(bvslt group_id_y$1 num_groups_y)
(bvslt group_id_y$2 num_groups_y)
(bvsge local_id_y$1 #x00000000)
(bvsge local_id_y$2 #x00000000)
(bvslt local_id_y$1 group_size_y)
(bvslt local_id_y$2 group_size_y)
(bvsgt group_size_z #x00000000)
(bvsgt num_groups_z #x00000000)
(bvsge group_id_z$1 #x00000000)
(bvsge group_id_z$2 #x00000000)
(bvslt group_id_z$1 num_groups_z)
(bvslt group_id_z$2 num_groups_z)
(bvsge local_id_z$1 #x00000000)
(bvsge local_id_z$2 #x00000000)
(bvslt local_id_z$1 group_size_z)
(bvslt local_id_z$2 group_size_z)
(=> (not _WRITE_HAS_OCCURRED_$$p$1) (= _WRITE_SOURCE_$$p$1 #x00000000))
(=> (not _READ_HAS_OCCURRED_$$p$1) (= _READ_SOURCE_$$p$1 #x00000000))
(=> _WRITE_HAS_OCCURRED_$$p$1 (or
(= _WRITE_SOURCE_$$p$1 #x00000001)
(= _WRITE_SOURCE_$$p$1 #x00000002)))
(=> _READ_HAS_OCCURRED_$$p$1 false)
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (or
(not (= local_id_x$1 local_id_x$2))
(not (= local_id_y$1 local_id_y$2))
(not (= local_id_z$1 local_id_z$2))))
(= (ControlFlow 0 1462) 1187)) inline$_LOG_WRITE_$$p$0$Entry_correct)))))
$0_correct)))))))))))))
(push 1)
(set-info :boogie-vc-id $foo)
(assert (not
(=> true $foo)
))
(check-sat)
;(get-value ((ControlFlow 0 0)))
; (get-value ((ControlFlow 0 1462)))
; (get-value ((ControlFlow 0 1187)))
; (get-value ((ControlFlow 0 1189)))
; (get-value ((ControlFlow 0 1334)))
; (get-value ((ControlFlow 0 1324)))
; (get-value ((ControlFlow 0 1328)))
; (get-value ((ControlFlow 0 1432)))
; (get-value ((ControlFlow 0 1434)))
; (get-value ((ControlFlow 0 1440)))
; (get-model)
; (assert (not (= (ControlFlow 0 1440) (- 3060))))
