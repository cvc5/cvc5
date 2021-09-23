; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
;(set-option :produce-unsat-cores true)
(set-option :print-success false)
(set-info :smt-lib-version 2.6)
;(set-option :produce-models true)
(set-logic ALL)
; done setting options

; Boogie universal background predicate
; Copyright (c) 2004-2010, Microsoft Corp.
(set-info :category "industrial")
(declare-sort |T@U| 0)
(declare-sort |T@T| 0)
(declare-fun int_div (Int Int) Int)
(declare-fun int_mod (Int Int) Int)
(declare-fun UOrdering2 (|T@U| |T@U|) Bool)
(declare-fun UOrdering3 (|T@T| |T@U| |T@U|) Bool)

(declare-fun group_size_y () (_ BitVec 32))
(declare-fun group_size_z () (_ BitVec 32))
(declare-fun num_groups_y () (_ BitVec 32))
(declare-fun num_groups_z () (_ BitVec 32))
(declare-fun group_size_x () (_ BitVec 32))
(declare-fun num_groups_x () (_ BitVec 32))
(declare-fun ControlFlow (Int Int) Int)
(declare-fun %lbl%+8971 () Bool)
(declare-fun call3746formal@_offset$2@0 () (_ BitVec 32))
(declare-fun v1$2@0 () (_ BitVec 32))
(declare-fun %lbl%@30054 () Bool)
(declare-fun _P$2 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$newVelocity$1@3 () Bool)
(declare-fun _WRITE_OFFSET_$$newVelocity$1@3 () (_ BitVec 32))
(declare-fun %lbl%@30066 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$newVelocity$1 () Bool)
(declare-fun _READ_OFFSET_$$newVelocity$1 () (_ BitVec 32))
(declare-fun %lbl%+8965 () Bool)
(declare-fun _P$1 () Bool)
(declare-fun inline$_LOG_WRITE_$$newVelocity$3$track@0 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$newVelocity$1@2 () Bool)
(declare-fun inline$_LOG_WRITE_$$newVelocity$3$_offset$1@0 () (_ BitVec 32))
(declare-fun _WRITE_OFFSET_$$newVelocity$1@2 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$newVelocity$1@3 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$newVelocity$1@2 () (_ BitVec 32))
(declare-fun %lbl%+8963 () Bool)
(declare-fun v1$1@0 () (_ BitVec 32))
(declare-fun %lbl%+8969 () Bool)
(declare-fun call3709formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@29931 () Bool)
(declare-fun %lbl%@29943 () Bool)
(declare-fun %lbl%@29957 () Bool)
(declare-fun %lbl%+8883 () Bool)
(declare-fun inline$_LOG_WRITE_$$newVelocity$2$track@0 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$newVelocity$1@1 () Bool)
(declare-fun inline$_LOG_WRITE_$$newVelocity$2$_offset$1@0 () (_ BitVec 32))
(declare-fun _WRITE_OFFSET_$$newVelocity$1@1 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$newVelocity$1@1 () (_ BitVec 32))
(declare-fun %lbl%+8881 () Bool)
(declare-fun %lbl%+8887 () Bool)
(declare-fun call3672formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@29808 () Bool)
(declare-fun %lbl%@29820 () Bool)
(declare-fun %lbl%@29834 () Bool)
(declare-fun %lbl%+8801 () Bool)
(declare-fun inline$_LOG_WRITE_$$newVelocity$1$track@0 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$newVelocity$1@0 () Bool)
(declare-fun inline$_LOG_WRITE_$$newVelocity$1$_offset$1@0 () (_ BitVec 32))
(declare-fun _WRITE_OFFSET_$$newVelocity$1@0 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$newVelocity$1@0 () (_ BitVec 32))
(declare-fun %lbl%+8799 () Bool)
(declare-fun %lbl%+8805 () Bool)
(declare-fun call3635formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@29685 () Bool)
(declare-fun %lbl%@29697 () Bool)
(declare-fun %lbl%@29711 () Bool)
(declare-fun %lbl%+8719 () Bool)
(declare-fun inline$_LOG_WRITE_$$newVelocity$0$track@0 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$newVelocity$1 () Bool)
(declare-fun inline$_LOG_WRITE_$$newVelocity$0$_offset$1@0 () (_ BitVec 32))
(declare-fun _WRITE_OFFSET_$$newVelocity$1 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$newVelocity$1 () (_ BitVec 32))
(declare-fun %lbl%+8717 () Bool)
(declare-fun %lbl%+8723 () Bool)
(declare-fun call3604formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@29564 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$newPosition$1@3 () Bool)
(declare-fun _WRITE_OFFSET_$$newPosition$1@3 () (_ BitVec 32))
(declare-fun %lbl%@29576 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$newPosition$1 () Bool)
(declare-fun _READ_OFFSET_$$newPosition$1 () (_ BitVec 32))
(declare-fun %lbl%@29590 () Bool)
(declare-fun %lbl%+8637 () Bool)
(declare-fun inline$_LOG_WRITE_$$newPosition$3$track@0 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$newPosition$1@2 () Bool)
(declare-fun inline$_LOG_WRITE_$$newPosition$3$_offset$1@0 () (_ BitVec 32))
(declare-fun _WRITE_OFFSET_$$newPosition$1@2 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$newPosition$1@3 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$newPosition$1@2 () (_ BitVec 32))
(declare-fun %lbl%+8635 () Bool)
(declare-fun %lbl%+8641 () Bool)
(declare-fun call3567formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@29441 () Bool)
(declare-fun %lbl%@29453 () Bool)
(declare-fun %lbl%@29467 () Bool)
(declare-fun %lbl%+8555 () Bool)
(declare-fun inline$_LOG_WRITE_$$newPosition$2$track@0 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$newPosition$1@1 () Bool)
(declare-fun inline$_LOG_WRITE_$$newPosition$2$_offset$1@0 () (_ BitVec 32))
(declare-fun _WRITE_OFFSET_$$newPosition$1@1 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$newPosition$1@1 () (_ BitVec 32))
(declare-fun %lbl%+8553 () Bool)
(declare-fun %lbl%+8559 () Bool)
(declare-fun call3530formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@29318 () Bool)
(declare-fun %lbl%@29330 () Bool)
(declare-fun %lbl%@29344 () Bool)
(declare-fun %lbl%+8473 () Bool)
(declare-fun inline$_LOG_WRITE_$$newPosition$1$track@0 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$newPosition$1@0 () Bool)
(declare-fun inline$_LOG_WRITE_$$newPosition$1$_offset$1@0 () (_ BitVec 32))
(declare-fun _WRITE_OFFSET_$$newPosition$1@0 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$newPosition$1@0 () (_ BitVec 32))
(declare-fun %lbl%+8471 () Bool)
(declare-fun %lbl%+8477 () Bool)
(declare-fun call3493formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@29195 () Bool)
(declare-fun %lbl%@29207 () Bool)
(declare-fun %lbl%@29221 () Bool)
(declare-fun %lbl%+8391 () Bool)
(declare-fun inline$_LOG_WRITE_$$newPosition$0$track@0 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$newPosition$1 () Bool)
(declare-fun inline$_LOG_WRITE_$$newPosition$0$_offset$1@0 () (_ BitVec 32))
(declare-fun _WRITE_OFFSET_$$newPosition$1 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$newPosition$1 () (_ BitVec 32))
(declare-fun %lbl%+8389 () Bool)
(declare-fun %lbl%+8395 () Bool)
(declare-fun call3462formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@29086 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$vel$1 () Bool)
(declare-fun _WRITE_OFFSET_$$vel$1 () (_ BitVec 32))
(declare-fun %lbl%@29100 () Bool)
(declare-fun %lbl%+8309 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$vel$1@3 () Bool)
(declare-fun inline$_LOG_READ_$$vel$3$track@0 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$vel$1@2 () Bool)
(declare-fun _READ_OFFSET_$$vel$1@3 () (_ BitVec 32))
(declare-fun inline$_LOG_READ_$$vel$3$_offset$1@0 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$vel$1@2 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$vel$1@3 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$vel$1@2 () (_ BitVec 32))
(declare-fun %lbl%+8307 () Bool)
(declare-fun %lbl%+8313 () Bool)
(declare-fun call3409formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@28944 () Bool)
(declare-fun %lbl%@28958 () Bool)
(declare-fun v26$1@0 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$1@18 () (_ BitVec 32))
(declare-fun v26$1 () (_ BitVec 32))
(declare-fun v26$2@0 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@18 () (_ BitVec 32))
(declare-fun v26$2 () (_ BitVec 32))
(declare-fun %lbl%+8227 () Bool)
(declare-fun inline$_LOG_READ_$$vel$2$track@0 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$vel$1@1 () Bool)
(declare-fun inline$_LOG_READ_$$vel$2$_offset$1@0 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$vel$1@1 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$vel$1@1 () (_ BitVec 32))
(declare-fun %lbl%+8225 () Bool)
(declare-fun %lbl%+8231 () Bool)
(declare-fun call3356formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@28802 () Bool)
(declare-fun %lbl%@28816 () Bool)
(declare-fun v25$1@0 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$1@17 () (_ BitVec 32))
(declare-fun v25$1 () (_ BitVec 32))
(declare-fun v25$2@0 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@17 () (_ BitVec 32))
(declare-fun v25$2 () (_ BitVec 32))
(declare-fun %lbl%+8145 () Bool)
(declare-fun inline$_LOG_READ_$$vel$1$track@0 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$vel$1@0 () Bool)
(declare-fun inline$_LOG_READ_$$vel$1$_offset$1@0 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$vel$1@0 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$vel$1@0 () (_ BitVec 32))
(declare-fun %lbl%+8143 () Bool)
(declare-fun %lbl%+8149 () Bool)
(declare-fun call3303formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@28660 () Bool)
(declare-fun %lbl%@28674 () Bool)
(declare-fun v24$1@0 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$1@16 () (_ BitVec 32))
(declare-fun v24$1 () (_ BitVec 32))
(declare-fun v24$2@0 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@16 () (_ BitVec 32))
(declare-fun v24$2 () (_ BitVec 32))
(declare-fun %lbl%+8063 () Bool)
(declare-fun inline$_LOG_READ_$$vel$0$track@0 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$vel$1 () Bool)
(declare-fun inline$_LOG_READ_$$vel$0$_offset$1@0 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$vel$1 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$vel$1 () (_ BitVec 32))
(declare-fun %lbl%+8061 () Bool)
(declare-fun %lbl%+8067 () Bool)
(declare-fun p0$1@3 () Bool)
(declare-fun p0$2@3 () Bool)
(declare-fun %lbl%@28534 () Bool)
(declare-fun v23$1@0 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$1@15 () (_ BitVec 32))
(declare-fun v23$1 () (_ BitVec 32))
(declare-fun v23$2@0 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@15 () (_ BitVec 32))
(declare-fun v23$2 () (_ BitVec 32))
(declare-fun %lbl%+8973 () Bool)
(declare-fun %lbl%@27591 () Bool)
(declare-fun _b10 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$localPos$1@4 () Bool)
(declare-fun _WRITE_OFFSET_$$localPos$1@4 () (_ BitVec 32))
(declare-fun local_id_x$1 () (_ BitVec 32))
(declare-fun %lbl%@27652 () Bool)
(declare-fun _b9 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$localPos$1@6 () Bool)
(declare-fun _READ_OFFSET_$$localPos$1@6 () (_ BitVec 32))
(declare-fun %lbl%@27848 () Bool)
(declare-fun _b8 () Bool)
(declare-fun %lbl%@27855 () Bool)
(declare-fun _b7 () Bool)
(declare-fun %lbl%@27862 () Bool)
(declare-fun _b6 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$pos$1@8 () Bool)
(declare-fun _READ_OFFSET_$$pos$1@8 () (_ BitVec 32))
(declare-fun %lbl%@28083 () Bool)
(declare-fun _b5 () Bool)
(declare-fun %lbl%@28090 () Bool)
(declare-fun _b4 () Bool)
(declare-fun $j.0$1@3 () (_ BitVec 32))
(declare-fun $j.0$2@3 () (_ BitVec 32))
(declare-fun %lbl%@28104 () Bool)
(declare-fun _b3 () Bool)
(declare-fun $acc.1$1@3 () (_ BitVec 128))
(declare-fun $acc.1$2@3 () (_ BitVec 128))
(declare-fun %lbl%@28118 () Bool)
(declare-fun _b2 () Bool)
(declare-fun $i.0$1@2 () (_ BitVec 32))
(declare-fun $i.0$2@2 () (_ BitVec 32))
(declare-fun %lbl%@28132 () Bool)
(declare-fun _b1 () Bool)
(declare-fun $acc.0$1@2 () (_ BitVec 128))
(declare-fun $acc.0$2@2 () (_ BitVec 128))
(declare-fun %lbl%@28146 () Bool)
(declare-fun _b0 () Bool)
(declare-fun %lbl%@28154 () Bool)
(declare-fun %lbl%@28188 () Bool)
(declare-fun %lbl%@28194 () Bool)
(declare-fun %lbl%@28206 () Bool)
(declare-fun _WRITE_SOURCE_$$vel$1 () (_ BitVec 32))
(declare-fun %lbl%@28218 () Bool)
(declare-fun _READ_SOURCE_$$pos$1@8 () (_ BitVec 32))
(declare-fun %lbl%@28275 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$pos$1 () Bool)
(declare-fun %lbl%@28281 () Bool)
(declare-fun %lbl%@28291 () Bool)
(declare-fun _WRITE_SOURCE_$$pos$1 () (_ BitVec 32))
(declare-fun %lbl%@28303 () Bool)
(declare-fun _READ_SOURCE_$$localPos$1@6 () (_ BitVec 32))
(declare-fun %lbl%@28339 () Bool)
(declare-fun _WRITE_SOURCE_$$localPos$1@4 () (_ BitVec 32))
(declare-fun %lbl%@28368 () Bool)
(declare-fun %lbl%@28378 () Bool)
(declare-fun %lbl%@28388 () Bool)
(declare-fun %lbl%@28394 () Bool)
(declare-fun %lbl%@28428 () Bool)
(declare-fun _READ_SOURCE_$$newVelocity$1 () (_ BitVec 32))
(declare-fun %lbl%@28440 () Bool)
(declare-fun %lbl%@28452 () Bool)
(declare-fun %lbl%@28458 () Bool)
(declare-fun %lbl%@28492 () Bool)
(declare-fun _READ_SOURCE_$$newPosition$1 () (_ BitVec 32))
(declare-fun %lbl%@28504 () Bool)
(declare-fun %lbl%@28516 () Bool)
(declare-fun %lbl%@28521 () Bool)
(declare-fun %lbl%+7985 () Bool)
(declare-fun p1$1@1 () Bool)
(declare-fun $acc.0$1@1 () (_ BitVec 128))
(declare-fun p1$2@1 () Bool)
(declare-fun $acc.0$2@1 () (_ BitVec 128))
(declare-fun $i.0$1@1 () (_ BitVec 32))
(declare-fun $i.0$2@1 () (_ BitVec 32))
(declare-fun p0$1@2 () Bool)
(declare-fun p0$2@2 () Bool)
(declare-fun %lbl%+7981 () Bool)
(declare-fun %lbl%+7969 () Bool)
(declare-fun inline$$bugle_barrier$1$$1$2@1 () (_ BitVec 1))
(declare-fun %lbl%+7971 () Bool)
(declare-fun %lbl%+7967 () Bool)
(declare-fun %lbl%+7965 () Bool)
(declare-fun inline$$bugle_barrier$1$$1$1@1 () (_ BitVec 1))
(declare-fun %lbl%+7973 () Bool)
(declare-fun group_id_x$1 () (_ BitVec 32))
(declare-fun group_id_x$2 () (_ BitVec 32))
(declare-fun group_id_y$1 () (_ BitVec 32))
(declare-fun group_id_y$2 () (_ BitVec 32))
(declare-fun group_id_z$1 () (_ BitVec 32))
(declare-fun group_id_z$2 () (_ BitVec 32))
(declare-fun %lbl%+7963 () Bool)
(declare-fun %lbl%+7961 () Bool)
(declare-fun inline$$bugle_barrier$1$$0$2@1 () (_ BitVec 1))
(declare-fun %lbl%+7975 () Bool)
(declare-fun %lbl%+7959 () Bool)
(declare-fun %lbl%+7957 () Bool)
(declare-fun inline$$bugle_barrier$1$$0$1@1 () (_ BitVec 1))
(declare-fun %lbl%+7977 () Bool)
(declare-fun %lbl%+7955 () Bool)
(declare-fun %lbl%+7979 () Bool)
(declare-fun %lbl%+7951 () Bool)
(declare-fun %lbl%@27100 () Bool)
(declare-fun %lbl%+7983 () Bool)
(declare-fun p2$1@4 () Bool)
(declare-fun p2$2@4 () Bool)
(declare-fun %lbl%+8975 () Bool)
(declare-fun %lbl%@26466 () Bool)
(declare-fun _b11 () Bool)
(declare-fun %lbl%@26662 () Bool)
(declare-fun %lbl%@26696 () Bool)
(declare-fun %lbl%@26702 () Bool)
(declare-fun %lbl%@26714 () Bool)
(declare-fun %lbl%@26726 () Bool)
(declare-fun %lbl%@26783 () Bool)
(declare-fun %lbl%@26789 () Bool)
(declare-fun %lbl%@26799 () Bool)
(declare-fun %lbl%@26811 () Bool)
(declare-fun %lbl%@26847 () Bool)
(declare-fun %lbl%@26876 () Bool)
(declare-fun %lbl%@26886 () Bool)
(declare-fun %lbl%@26896 () Bool)
(declare-fun %lbl%@26902 () Bool)
(declare-fun %lbl%@26936 () Bool)
(declare-fun %lbl%@26948 () Bool)
(declare-fun %lbl%@26960 () Bool)
(declare-fun %lbl%@26966 () Bool)
(declare-fun %lbl%@27000 () Bool)
(declare-fun %lbl%@27012 () Bool)
(declare-fun %lbl%@27024 () Bool)
(declare-fun %lbl%@27028 () Bool)
(declare-fun %lbl%+7448 () Bool)
(declare-fun call3008formal@_offset$2@0 () (_ BitVec 32))
(declare-fun $j.0$2@2 () (_ BitVec 32))
(declare-fun %lbl%@26241 () Bool)
(declare-fun p3$2@2 () Bool)
(declare-fun v22$1@2 () (_ BitVec 32))
(declare-fun p3$1@2 () Bool)
(declare-fun FMUL32 ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
(declare-fun v21$1@2 () (_ BitVec 32))
(declare-fun v20$1@2 () (_ BitVec 32))
(declare-fun v22$1@1 () (_ BitVec 32))
(declare-fun v22$2@2 () (_ BitVec 32))
(declare-fun v21$2@2 () (_ BitVec 32))
(declare-fun v20$2@2 () (_ BitVec 32))
(declare-fun v22$2@1 () (_ BitVec 32))
(declare-fun FADD32 ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
(declare-fun $acc.1$1@2 () (_ BitVec 128))
(declare-fun FSUB32 ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
(declare-fun v16$1@2 () (_ BitVec 32))
(declare-fun v6$1@0 () (_ BitVec 32))
(declare-fun v19$1@2 () (_ BitVec 32))
(declare-fun v18$1@2 () (_ BitVec 32))
(declare-fun v17$1@2 () (_ BitVec 32))
(declare-fun $acc.1$2@2 () (_ BitVec 128))
(declare-fun v16$2@2 () (_ BitVec 32))
(declare-fun v6$2@0 () (_ BitVec 32))
(declare-fun v19$2@2 () (_ BitVec 32))
(declare-fun v18$2@2 () (_ BitVec 32))
(declare-fun v17$2@2 () (_ BitVec 32))
(declare-fun $j.0$1@2 () (_ BitVec 32))
(declare-fun p2$1@3 () Bool)
(declare-fun p2$2@3 () Bool)
(declare-fun %lbl%+7442 () Bool)
(declare-fun inline$_LOG_READ_$$localPos$4$track@2 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$localPos$1@5 () Bool)
(declare-fun inline$_LOG_READ_$$localPos$4$_offset$1@2 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$localPos$1@5 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$localPos$1@5 () (_ BitVec 32))
(declare-fun %lbl%+7440 () Bool)
(declare-fun %lbl%+7446 () Bool)
(declare-fun call2839formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@25932 () Bool)
(declare-fun v13$1@2 () (_ BitVec 32))
(declare-fun v3$1@0 () (_ BitVec 32))
(declare-fun v17$1@1 () (_ BitVec 32))
(declare-fun v13$2@2 () (_ BitVec 32))
(declare-fun v3$2@0 () (_ BitVec 32))
(declare-fun v17$2@1 () (_ BitVec 32))
(declare-fun v14$1@2 () (_ BitVec 32))
(declare-fun v4$1@0 () (_ BitVec 32))
(declare-fun v18$1@1 () (_ BitVec 32))
(declare-fun v14$2@2 () (_ BitVec 32))
(declare-fun v4$2@0 () (_ BitVec 32))
(declare-fun v18$2@1 () (_ BitVec 32))
(declare-fun v15$1@2 () (_ BitVec 32))
(declare-fun v5$1@0 () (_ BitVec 32))
(declare-fun v19$1@1 () (_ BitVec 32))
(declare-fun v15$2@2 () (_ BitVec 32))
(declare-fun v5$2@0 () (_ BitVec 32))
(declare-fun v19$2@1 () (_ BitVec 32))
(declare-fun FDIV32 ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
(declare-fun FSQRT32 ((_ BitVec 32)) (_ BitVec 32))
(declare-fun $epsSqr$1 () (_ BitVec 32))
(declare-fun v20$1@1 () (_ BitVec 32))
(declare-fun $epsSqr$2 () (_ BitVec 32))
(declare-fun v20$2@1 () (_ BitVec 32))
(declare-fun %lbl%@26120 () Bool)
(declare-fun _HAVOC_bv32$1@14 () (_ BitVec 32))
(declare-fun v21$1@1 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@14 () (_ BitVec 32))
(declare-fun v21$2@1 () (_ BitVec 32))
(declare-fun %lbl%+7360 () Bool)
(declare-fun inline$_LOG_READ_$$localPos$3$track@2 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$localPos$1@4 () Bool)
(declare-fun inline$_LOG_READ_$$localPos$3$_offset$1@2 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$localPos$1@4 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$localPos$1@4 () (_ BitVec 32))
(declare-fun %lbl%+7358 () Bool)
(declare-fun %lbl%+7364 () Bool)
(declare-fun call2786formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@25775 () Bool)
(declare-fun %lbl%@25811 () Bool)
(declare-fun _HAVOC_bv32$1@13 () (_ BitVec 32))
(declare-fun v16$1@1 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@13 () (_ BitVec 32))
(declare-fun v16$2@1 () (_ BitVec 32))
(declare-fun %lbl%+7278 () Bool)
(declare-fun inline$_LOG_READ_$$localPos$2$track@2 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$localPos$1@3 () Bool)
(declare-fun inline$_LOG_READ_$$localPos$2$_offset$1@2 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$localPos$1@3 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$localPos$1@3 () (_ BitVec 32))
(declare-fun %lbl%+7276 () Bool)
(declare-fun %lbl%+7282 () Bool)
(declare-fun call2733formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@25618 () Bool)
(declare-fun %lbl%@25654 () Bool)
(declare-fun _HAVOC_bv32$1@12 () (_ BitVec 32))
(declare-fun v15$1@1 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@12 () (_ BitVec 32))
(declare-fun v15$2@1 () (_ BitVec 32))
(declare-fun %lbl%+7196 () Bool)
(declare-fun inline$_LOG_READ_$$localPos$1$track@2 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$localPos$1@2 () Bool)
(declare-fun inline$_LOG_READ_$$localPos$1$_offset$1@2 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$localPos$1@2 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$localPos$1@2 () (_ BitVec 32))
(declare-fun %lbl%+7194 () Bool)
(declare-fun %lbl%+7200 () Bool)
(declare-fun call2680formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@25461 () Bool)
(declare-fun %lbl%@25497 () Bool)
(declare-fun _HAVOC_bv32$1@11 () (_ BitVec 32))
(declare-fun v14$1@1 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@11 () (_ BitVec 32))
(declare-fun v14$2@1 () (_ BitVec 32))
(declare-fun %lbl%+7114 () Bool)
(declare-fun inline$_LOG_READ_$$localPos$0$track@2 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$localPos$1@1 () Bool)
(declare-fun inline$_LOG_READ_$$localPos$0$_offset$1@2 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$localPos$1@1 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$localPos$1@1 () (_ BitVec 32))
(declare-fun %lbl%+7112 () Bool)
(declare-fun %lbl%+7118 () Bool)
(declare-fun p2$1@2 () Bool)
(declare-fun p2$2@2 () Bool)
(declare-fun v12$1@2 () Bool)
(declare-fun v2$1@0 () (_ BitVec 32))
(declare-fun v12$1@1 () Bool)
(declare-fun v12$2@2 () Bool)
(declare-fun v2$2@0 () (_ BitVec 32))
(declare-fun v12$2@1 () Bool)
(declare-fun %lbl%@25348 () Bool)
(declare-fun _HAVOC_bv32$1@10 () (_ BitVec 32))
(declare-fun v13$1@1 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@10 () (_ BitVec 32))
(declare-fun v13$2@1 () (_ BitVec 32))
(declare-fun %lbl%+7036 () Bool)
(declare-fun $acc.1$1@1 () (_ BitVec 128))
(declare-fun $acc.1$1@0 () (_ BitVec 128))
(declare-fun $acc.1$2@1 () (_ BitVec 128))
(declare-fun $acc.1$2@0 () (_ BitVec 128))
(declare-fun $j.0$1@1 () (_ BitVec 32))
(declare-fun $j.0$1@0 () (_ BitVec 32))
(declare-fun $j.0$2@1 () (_ BitVec 32))
(declare-fun $j.0$2@0 () (_ BitVec 32))
(declare-fun p2$1@1 () Bool)
(declare-fun p2$2@1 () Bool)
(declare-fun %lbl%@23930 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$localPos$1@0 () Bool)
(declare-fun _READ_OFFSET_$$localPos$1@0 () (_ BitVec 32))
(declare-fun %lbl%@24126 () Bool)
(declare-fun %lbl%@24160 () Bool)
(declare-fun %lbl%@24166 () Bool)
(declare-fun %lbl%@24178 () Bool)
(declare-fun %lbl%@24190 () Bool)
(declare-fun %lbl%@24247 () Bool)
(declare-fun %lbl%@24253 () Bool)
(declare-fun %lbl%@24263 () Bool)
(declare-fun %lbl%@24275 () Bool)
(declare-fun _READ_SOURCE_$$localPos$1@0 () (_ BitVec 32))
(declare-fun %lbl%@24311 () Bool)
(declare-fun %lbl%@24340 () Bool)
(declare-fun %lbl%@24350 () Bool)
(declare-fun %lbl%@24360 () Bool)
(declare-fun %lbl%@24366 () Bool)
(declare-fun %lbl%@24400 () Bool)
(declare-fun %lbl%@24412 () Bool)
(declare-fun %lbl%@24424 () Bool)
(declare-fun %lbl%@24430 () Bool)
(declare-fun %lbl%@24464 () Bool)
(declare-fun %lbl%@24476 () Bool)
(declare-fun %lbl%@24488 () Bool)
(declare-fun %lbl%@24492 () Bool)
(declare-fun %lbl%+7032 () Bool)
(declare-fun %lbl%+7020 () Bool)
(declare-fun inline$$bugle_barrier$0$$1$2@1 () (_ BitVec 1))
(declare-fun %lbl%+7022 () Bool)
(declare-fun %lbl%+7018 () Bool)
(declare-fun %lbl%+7016 () Bool)
(declare-fun inline$$bugle_barrier$0$$1$1@1 () (_ BitVec 1))
(declare-fun %lbl%+7024 () Bool)
(declare-fun %lbl%+7014 () Bool)
(declare-fun %lbl%+7012 () Bool)
(declare-fun inline$$bugle_barrier$0$$0$2@1 () (_ BitVec 1))
(declare-fun %lbl%+7026 () Bool)
(declare-fun %lbl%+7010 () Bool)
(declare-fun %lbl%+7008 () Bool)
(declare-fun inline$$bugle_barrier$0$$0$1@1 () (_ BitVec 1))
(declare-fun %lbl%+7028 () Bool)
(declare-fun %lbl%+7006 () Bool)
(declare-fun %lbl%+7030 () Bool)
(declare-fun %lbl%+7002 () Bool)
(declare-fun %lbl%@23449 () Bool)
(declare-fun %lbl%+7034 () Bool)
(declare-fun call2152formal@_offset$2@0 () (_ BitVec 32))
(declare-fun v0$2@0 () (_ BitVec 32))
(declare-fun %lbl%@23317 () Bool)
(declare-fun %lbl%@23353 () Bool)
(declare-fun %lbl%+6495 () Bool)
(declare-fun inline$_LOG_WRITE_$$localPos$3$track@1 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$localPos$1@3 () Bool)
(declare-fun inline$_LOG_WRITE_$$localPos$3$_offset$1@1 () (_ BitVec 32))
(declare-fun _WRITE_OFFSET_$$localPos$1@3 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$localPos$1@3 () (_ BitVec 32))
(declare-fun %lbl%+6493 () Bool)
(declare-fun v0$1@0 () (_ BitVec 32))
(declare-fun %lbl%+6499 () Bool)
(declare-fun call2115formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@23151 () Bool)
(declare-fun %lbl%@23187 () Bool)
(declare-fun %lbl%@23223 () Bool)
(declare-fun %lbl%+6413 () Bool)
(declare-fun inline$_LOG_WRITE_$$localPos$2$track@1 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$localPos$1@2 () Bool)
(declare-fun inline$_LOG_WRITE_$$localPos$2$_offset$1@1 () (_ BitVec 32))
(declare-fun _WRITE_OFFSET_$$localPos$1@2 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$localPos$1@2 () (_ BitVec 32))
(declare-fun %lbl%+6411 () Bool)
(declare-fun %lbl%+6417 () Bool)
(declare-fun call2078formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@22985 () Bool)
(declare-fun %lbl%@23021 () Bool)
(declare-fun %lbl%@23057 () Bool)
(declare-fun %lbl%+6331 () Bool)
(declare-fun inline$_LOG_WRITE_$$localPos$1$track@1 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$localPos$1@1 () Bool)
(declare-fun inline$_LOG_WRITE_$$localPos$1$_offset$1@1 () (_ BitVec 32))
(declare-fun _WRITE_OFFSET_$$localPos$1@1 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$localPos$1@1 () (_ BitVec 32))
(declare-fun %lbl%+6329 () Bool)
(declare-fun %lbl%+6335 () Bool)
(declare-fun call2041formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@22819 () Bool)
(declare-fun %lbl%@22855 () Bool)
(declare-fun %lbl%@22891 () Bool)
(declare-fun %lbl%+6249 () Bool)
(declare-fun inline$_LOG_WRITE_$$localPos$0$track@1 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$localPos$1@0 () Bool)
(declare-fun inline$_LOG_WRITE_$$localPos$0$_offset$1@1 () (_ BitVec 32))
(declare-fun _WRITE_OFFSET_$$localPos$1@0 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$localPos$1@0 () (_ BitVec 32))
(declare-fun %lbl%+6247 () Bool)
(declare-fun %lbl%+6253 () Bool)
(declare-fun call2010formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@22719 () Bool)
(declare-fun _WRITE_OFFSET_$$pos$1 () (_ BitVec 32))
(declare-fun %lbl%@22733 () Bool)
(declare-fun %lbl%+6167 () Bool)
(declare-fun inline$_LOG_READ_$$pos$7$track@1 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$pos$1@7 () Bool)
(declare-fun inline$_LOG_READ_$$pos$7$_offset$1@1 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$pos$1@7 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$pos$1@7 () (_ BitVec 32))
(declare-fun %lbl%+6165 () Bool)
(declare-fun %lbl%+6171 () Bool)
(declare-fun call1945formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@22572 () Bool)
(declare-fun %lbl%@22586 () Bool)
(declare-fun v11$1@1 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$1@8 () (_ BitVec 32))
(declare-fun v11$1@0 () (_ BitVec 32))
(declare-fun v11$2@1 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@8 () (_ BitVec 32))
(declare-fun v11$2@0 () (_ BitVec 32))
(declare-fun %lbl%+6085 () Bool)
(declare-fun inline$_LOG_READ_$$pos$6$track@1 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$pos$1@6 () Bool)
(declare-fun inline$_LOG_READ_$$pos$6$_offset$1@1 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$pos$1@6 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$pos$1@6 () (_ BitVec 32))
(declare-fun %lbl%+6083 () Bool)
(declare-fun %lbl%+6089 () Bool)
(declare-fun call1880formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@22425 () Bool)
(declare-fun %lbl%@22439 () Bool)
(declare-fun v10$1@1 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$1@7 () (_ BitVec 32))
(declare-fun v10$1@0 () (_ BitVec 32))
(declare-fun v10$2@1 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@7 () (_ BitVec 32))
(declare-fun v10$2@0 () (_ BitVec 32))
(declare-fun %lbl%+6003 () Bool)
(declare-fun inline$_LOG_READ_$$pos$5$track@1 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$pos$1@5 () Bool)
(declare-fun inline$_LOG_READ_$$pos$5$_offset$1@1 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$pos$1@5 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$pos$1@5 () (_ BitVec 32))
(declare-fun %lbl%+6001 () Bool)
(declare-fun %lbl%+6007 () Bool)
(declare-fun call1815formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@22278 () Bool)
(declare-fun %lbl%@22292 () Bool)
(declare-fun v9$1@1 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$1@6 () (_ BitVec 32))
(declare-fun v9$1@0 () (_ BitVec 32))
(declare-fun v9$2@1 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@6 () (_ BitVec 32))
(declare-fun v9$2@0 () (_ BitVec 32))
(declare-fun %lbl%+5921 () Bool)
(declare-fun inline$_LOG_READ_$$pos$4$track@1 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$pos$1@4 () Bool)
(declare-fun inline$_LOG_READ_$$pos$4$_offset$1@1 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$pos$1@4 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$pos$1@4 () (_ BitVec 32))
(declare-fun %lbl%+5919 () Bool)
(declare-fun %lbl%+5925 () Bool)
(declare-fun p0$1@1 () Bool)
(declare-fun p0$2@1 () Bool)
(declare-fun v7$1@1 () Bool)
(declare-fun $numBodies$1 () (_ BitVec 32))
(declare-fun v7$1@0 () Bool)
(declare-fun v7$2@1 () Bool)
(declare-fun $numBodies$2 () (_ BitVec 32))
(declare-fun v7$2@0 () Bool)
(declare-fun %lbl%@22153 () Bool)
(declare-fun v8$1@1 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$1@5 () (_ BitVec 32))
(declare-fun v8$1@0 () (_ BitVec 32))
(declare-fun v8$2@1 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@5 () (_ BitVec 32))
(declare-fun v8$2@0 () (_ BitVec 32))
(declare-fun %lbl%+5843 () Bool)
(declare-fun call1006formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@19579 () Bool)
(declare-fun $acc.0$1@0 () (_ BitVec 128))
(declare-fun $acc.0$1 () (_ BitVec 128))
(declare-fun $acc.0$2@0 () (_ BitVec 128))
(declare-fun $acc.0$2 () (_ BitVec 128))
(declare-fun $i.0$1@0 () (_ BitVec 32))
(declare-fun $i.0$1 () (_ BitVec 32))
(declare-fun $i.0$2@0 () (_ BitVec 32))
(declare-fun $i.0$2 () (_ BitVec 32))
(declare-fun p0$1@0 () Bool)
(declare-fun p0$2@0 () Bool)
(declare-fun %lbl%@19676 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$localPos$1 () Bool)
(declare-fun _WRITE_OFFSET_$$localPos$1 () (_ BitVec 32))
(declare-fun %lbl%@19742 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$localPos$1 () Bool)
(declare-fun _READ_OFFSET_$$localPos$1 () (_ BitVec 32))
(declare-fun %lbl%@19944 () Bool)
(declare-fun %lbl%@19952 () Bool)
(declare-fun %lbl%@19960 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$pos$1@3 () Bool)
(declare-fun _READ_OFFSET_$$pos$1@3 () (_ BitVec 32))
(declare-fun %lbl%@20181 () Bool)
(declare-fun %lbl%@20188 () Bool)
(declare-fun $j.0$1 () (_ BitVec 32))
(declare-fun $j.0$2 () (_ BitVec 32))
(declare-fun %lbl%@20204 () Bool)
(declare-fun $acc.1$1 () (_ BitVec 128))
(declare-fun $acc.1$2 () (_ BitVec 128))
(declare-fun %lbl%@20220 () Bool)
(declare-fun %lbl%@20234 () Bool)
(declare-fun %lbl%@20248 () Bool)
(declare-fun %lbl%@20256 () Bool)
(declare-fun %lbl%@20290 () Bool)
(declare-fun %lbl%@20296 () Bool)
(declare-fun %lbl%@20308 () Bool)
(declare-fun %lbl%@20320 () Bool)
(declare-fun _READ_SOURCE_$$pos$1@3 () (_ BitVec 32))
(declare-fun %lbl%@20377 () Bool)
(declare-fun %lbl%@20383 () Bool)
(declare-fun %lbl%@20393 () Bool)
(declare-fun %lbl%@20405 () Bool)
(declare-fun _READ_SOURCE_$$localPos$1 () (_ BitVec 32))
(declare-fun %lbl%@20447 () Bool)
(declare-fun _WRITE_SOURCE_$$localPos$1 () (_ BitVec 32))
(declare-fun %lbl%@20481 () Bool)
(declare-fun %lbl%@20493 () Bool)
(declare-fun %lbl%@20505 () Bool)
(declare-fun %lbl%@20511 () Bool)
(declare-fun %lbl%@20545 () Bool)
(declare-fun %lbl%@20557 () Bool)
(declare-fun %lbl%@20569 () Bool)
(declare-fun %lbl%@20575 () Bool)
(declare-fun %lbl%@20609 () Bool)
(declare-fun %lbl%@20621 () Bool)
(declare-fun %lbl%@20633 () Bool)
(declare-fun %lbl%@20638 () Bool)
(declare-fun %lbl%+5837 () Bool)
(declare-fun inline$_LOG_READ_$$pos$3$track@0 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$pos$1@2 () Bool)
(declare-fun inline$_LOG_READ_$$pos$3$_offset$1@0 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$pos$1@2 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$pos$1@2 () (_ BitVec 32))
(declare-fun %lbl%+5835 () Bool)
(declare-fun %lbl%+5841 () Bool)
(declare-fun call953formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@19437 () Bool)
(declare-fun %lbl%@19451 () Bool)
(declare-fun _HAVOC_bv32$1@3 () (_ BitVec 32))
(declare-fun v6$1 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@3 () (_ BitVec 32))
(declare-fun v6$2 () (_ BitVec 32))
(declare-fun %lbl%+5755 () Bool)
(declare-fun inline$_LOG_READ_$$pos$2$track@0 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$pos$1@1 () Bool)
(declare-fun inline$_LOG_READ_$$pos$2$_offset$1@0 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$pos$1@1 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$pos$1@1 () (_ BitVec 32))
(declare-fun %lbl%+5753 () Bool)
(declare-fun %lbl%+5759 () Bool)
(declare-fun call900formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@19295 () Bool)
(declare-fun %lbl%@19309 () Bool)
(declare-fun _HAVOC_bv32$1@2 () (_ BitVec 32))
(declare-fun v5$1 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@2 () (_ BitVec 32))
(declare-fun v5$2 () (_ BitVec 32))
(declare-fun %lbl%+5673 () Bool)
(declare-fun inline$_LOG_READ_$$pos$1$track@0 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$pos$1@0 () Bool)
(declare-fun inline$_LOG_READ_$$pos$1$_offset$1@0 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$pos$1@0 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$pos$1@0 () (_ BitVec 32))
(declare-fun %lbl%+5671 () Bool)
(declare-fun %lbl%+5677 () Bool)
(declare-fun call847formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@19153 () Bool)
(declare-fun %lbl%@19167 () Bool)
(declare-fun _HAVOC_bv32$1@1 () (_ BitVec 32))
(declare-fun v4$1 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@1 () (_ BitVec 32))
(declare-fun v4$2 () (_ BitVec 32))
(declare-fun %lbl%+5591 () Bool)
(declare-fun inline$_LOG_READ_$$pos$0$track@0 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$pos$1 () Bool)
(declare-fun inline$_LOG_READ_$$pos$0$_offset$1@0 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$pos$1 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$pos$1 () (_ BitVec 32))
(declare-fun %lbl%+5589 () Bool)
(declare-fun %lbl%+5595 () Bool)
(declare-fun v0$1 () (_ BitVec 32))
(declare-fun local_id_x$2 () (_ BitVec 32))
(declare-fun v0$2 () (_ BitVec 32))
(declare-fun v1$1 () (_ BitVec 32))
(declare-fun v1$2 () (_ BitVec 32))
(declare-fun v2$1 () (_ BitVec 32))
(declare-fun v2$2 () (_ BitVec 32))
(declare-fun %lbl%@19027 () Bool)
(declare-fun _HAVOC_bv32$1@0 () (_ BitVec 32))
(declare-fun v3$1 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@0 () (_ BitVec 32))
(declare-fun v3$2 () (_ BitVec 32))
(declare-fun %lbl%+17409 () Bool)
(declare-fun local_id_y$1 () (_ BitVec 32))
(declare-fun local_id_y$2 () (_ BitVec 32))
(declare-fun local_id_z$1 () (_ BitVec 32))
(declare-fun local_id_z$2 () (_ BitVec 32))
(declare-fun $deltaTime$1 () (_ BitVec 32))
(declare-fun $deltaTime$2 () (_ BitVec 32))
(assert (not (= (ite (= group_size_y #x00000001) #b1 #b0) #b0)))
(assert (not (= (ite (= group_size_z #x00000001) #b1 #b0) #b0)))
(assert (not (= (ite (= num_groups_y #x00000001) #b1 #b0) #b0)))
(assert (not (= (ite (= num_groups_z #x00000001) #b1 #b0) #b0)))
(assert (not (= (ite (= group_size_x #x00000100) #b1 #b0) #b0)))
(assert (not (= (ite (= num_groups_x #x00000004) #b1 #b0) #b0)))
(define-fun $nbody_sim () Bool (=> (= (ControlFlow 0 0) 17409) (let (($for.cond.tail$12_correct (=> (and %lbl%+8971 true) (=> (= call3746formal@_offset$2@0 (bvadd (bvmul v1$2@0 #x00000004) #x00000003)) (and
(or %lbl%@30054 (=> (= (ControlFlow 0 8971) (- 0 30054)) (not (and
_P$2
_WRITE_HAS_OCCURRED_$$newVelocity$1@3
(= _WRITE_OFFSET_$$newVelocity$1@3 call3746formal@_offset$2@0)))))
(=> (not (and
_P$2
_WRITE_HAS_OCCURRED_$$newVelocity$1@3
(= _WRITE_OFFSET_$$newVelocity$1@3 call3746formal@_offset$2@0))) (and
(or %lbl%@30066 (=> (= (ControlFlow 0 8971) (- 0 30066)) (not (and
_P$2
_READ_HAS_OCCURRED_$$newVelocity$1
(= _READ_OFFSET_$$newVelocity$1 call3746formal@_offset$2@0)))))
(=> (not (and
_P$2
_READ_HAS_OCCURRED_$$newVelocity$1
(= _READ_OFFSET_$$newVelocity$1 call3746formal@_offset$2@0))) true))))))))
(let ((inline$_LOG_WRITE_$$newVelocity$3$_LOG_WRITE_correct (=> (and %lbl%+8965 true) (=> (and
(= _WRITE_HAS_OCCURRED_$$newVelocity$1@3 (ite (and
_P$1
inline$_LOG_WRITE_$$newVelocity$3$track@0) true _WRITE_HAS_OCCURRED_$$newVelocity$1@2))
(= _WRITE_OFFSET_$$newVelocity$1@3 (ite (and
_P$1
inline$_LOG_WRITE_$$newVelocity$3$track@0) inline$_LOG_WRITE_$$newVelocity$3$_offset$1@0 _WRITE_OFFSET_$$newVelocity$1@2))
(= _WRITE_SOURCE_$$newVelocity$1@3 (ite (and
_P$1
inline$_LOG_WRITE_$$newVelocity$3$track@0) #x00000010 _WRITE_SOURCE_$$newVelocity$1@2))
(= (ControlFlow 0 8965) 8971)) $for.cond.tail$12_correct))))
(let ((inline$_LOG_WRITE_$$newVelocity$3$Entry_correct (=> (and %lbl%+8963 true) (=> (and
(= inline$_LOG_WRITE_$$newVelocity$3$_offset$1@0 (bvadd (bvmul v1$1@0 #x00000004) #x00000003))
(= (ControlFlow 0 8963) 8965)) inline$_LOG_WRITE_$$newVelocity$3$_LOG_WRITE_correct))))
(let (($for.cond.tail$11_correct (=> (and %lbl%+8969 true) (=> (= call3709formal@_offset$2@0 (bvadd (bvmul v1$2@0 #x00000004) #x00000002)) (and
(or %lbl%@29931 (=> (= (ControlFlow 0 8969) (- 0 29931)) (not (and
_P$2
_WRITE_HAS_OCCURRED_$$newVelocity$1@2
(= _WRITE_OFFSET_$$newVelocity$1@2 call3709formal@_offset$2@0)))))
(=> (not (and
_P$2
_WRITE_HAS_OCCURRED_$$newVelocity$1@2
(= _WRITE_OFFSET_$$newVelocity$1@2 call3709formal@_offset$2@0))) (and
(or %lbl%@29943 (=> (= (ControlFlow 0 8969) (- 0 29943)) (not (and
_P$2
_READ_HAS_OCCURRED_$$newVelocity$1
(= _READ_OFFSET_$$newVelocity$1 call3709formal@_offset$2@0)))))
(=> (not (and
_P$2
_READ_HAS_OCCURRED_$$newVelocity$1
(= _READ_OFFSET_$$newVelocity$1 call3709formal@_offset$2@0))) (and
(or %lbl%@29957 (=> (= (ControlFlow 0 8969) (- 0 29957)) (=> _P$1 true)))
(=> (=> _P$1 true) (=> (= (ControlFlow 0 8969) 8963) inline$_LOG_WRITE_$$newVelocity$3$Entry_correct)))))))))))
(let ((inline$_LOG_WRITE_$$newVelocity$2$_LOG_WRITE_correct (=> (and %lbl%+8883 true) (=> (and
(= _WRITE_HAS_OCCURRED_$$newVelocity$1@2 (ite (and
_P$1
inline$_LOG_WRITE_$$newVelocity$2$track@0) true _WRITE_HAS_OCCURRED_$$newVelocity$1@1))
(= _WRITE_OFFSET_$$newVelocity$1@2 (ite (and
_P$1
inline$_LOG_WRITE_$$newVelocity$2$track@0) inline$_LOG_WRITE_$$newVelocity$2$_offset$1@0 _WRITE_OFFSET_$$newVelocity$1@1))
(= _WRITE_SOURCE_$$newVelocity$1@2 (ite (and
_P$1
inline$_LOG_WRITE_$$newVelocity$2$track@0) #x0000000f _WRITE_SOURCE_$$newVelocity$1@1))
(= (ControlFlow 0 8883) 8969)) $for.cond.tail$11_correct))))
(let ((inline$_LOG_WRITE_$$newVelocity$2$Entry_correct (=> (and %lbl%+8881 true) (=> (and
(= inline$_LOG_WRITE_$$newVelocity$2$_offset$1@0 (bvadd (bvmul v1$1@0 #x00000004) #x00000002))
(= (ControlFlow 0 8881) 8883)) inline$_LOG_WRITE_$$newVelocity$2$_LOG_WRITE_correct))))
(let (($for.cond.tail$10_correct (=> (and %lbl%+8887 true) (=> (= call3672formal@_offset$2@0 (bvadd (bvmul v1$2@0 #x00000004) #x00000001)) (and
(or %lbl%@29808 (=> (= (ControlFlow 0 8887) (- 0 29808)) (not (and
_P$2
_WRITE_HAS_OCCURRED_$$newVelocity$1@1
(= _WRITE_OFFSET_$$newVelocity$1@1 call3672formal@_offset$2@0)))))
(=> (not (and
_P$2
_WRITE_HAS_OCCURRED_$$newVelocity$1@1
(= _WRITE_OFFSET_$$newVelocity$1@1 call3672formal@_offset$2@0))) (and
(or %lbl%@29820 (=> (= (ControlFlow 0 8887) (- 0 29820)) (not (and
_P$2
_READ_HAS_OCCURRED_$$newVelocity$1
(= _READ_OFFSET_$$newVelocity$1 call3672formal@_offset$2@0)))))
(=> (not (and
_P$2
_READ_HAS_OCCURRED_$$newVelocity$1
(= _READ_OFFSET_$$newVelocity$1 call3672formal@_offset$2@0))) (and
(or %lbl%@29834 (=> (= (ControlFlow 0 8887) (- 0 29834)) (=> _P$1 true)))
(=> (=> _P$1 true) (=> (= (ControlFlow 0 8887) 8881) inline$_LOG_WRITE_$$newVelocity$2$Entry_correct)))))))))))
(let ((inline$_LOG_WRITE_$$newVelocity$1$_LOG_WRITE_correct (=> (and %lbl%+8801 true) (=> (and
(= _WRITE_HAS_OCCURRED_$$newVelocity$1@1 (ite (and
_P$1
inline$_LOG_WRITE_$$newVelocity$1$track@0) true _WRITE_HAS_OCCURRED_$$newVelocity$1@0))
(= _WRITE_OFFSET_$$newVelocity$1@1 (ite (and
_P$1
inline$_LOG_WRITE_$$newVelocity$1$track@0) inline$_LOG_WRITE_$$newVelocity$1$_offset$1@0 _WRITE_OFFSET_$$newVelocity$1@0))
(= _WRITE_SOURCE_$$newVelocity$1@1 (ite (and
_P$1
inline$_LOG_WRITE_$$newVelocity$1$track@0) #x0000000e _WRITE_SOURCE_$$newVelocity$1@0))
(= (ControlFlow 0 8801) 8887)) $for.cond.tail$10_correct))))
(let ((inline$_LOG_WRITE_$$newVelocity$1$Entry_correct (=> (and %lbl%+8799 true) (=> (and
(= inline$_LOG_WRITE_$$newVelocity$1$_offset$1@0 (bvadd (bvmul v1$1@0 #x00000004) #x00000001))
(= (ControlFlow 0 8799) 8801)) inline$_LOG_WRITE_$$newVelocity$1$_LOG_WRITE_correct))))
(let (($for.cond.tail$9_correct (=> (and %lbl%+8805 true) (=> (= call3635formal@_offset$2@0 (bvmul v1$2@0 #x00000004)) (and
(or %lbl%@29685 (=> (= (ControlFlow 0 8805) (- 0 29685)) (not (and
_P$2
_WRITE_HAS_OCCURRED_$$newVelocity$1@0
(= _WRITE_OFFSET_$$newVelocity$1@0 call3635formal@_offset$2@0)))))
(=> (not (and
_P$2
_WRITE_HAS_OCCURRED_$$newVelocity$1@0
(= _WRITE_OFFSET_$$newVelocity$1@0 call3635formal@_offset$2@0))) (and
(or %lbl%@29697 (=> (= (ControlFlow 0 8805) (- 0 29697)) (not (and
_P$2
_READ_HAS_OCCURRED_$$newVelocity$1
(= _READ_OFFSET_$$newVelocity$1 call3635formal@_offset$2@0)))))
(=> (not (and
_P$2
_READ_HAS_OCCURRED_$$newVelocity$1
(= _READ_OFFSET_$$newVelocity$1 call3635formal@_offset$2@0))) (and
(or %lbl%@29711 (=> (= (ControlFlow 0 8805) (- 0 29711)) (=> _P$1 true)))
(=> (=> _P$1 true) (=> (= (ControlFlow 0 8805) 8799) inline$_LOG_WRITE_$$newVelocity$1$Entry_correct)))))))))))
(let ((inline$_LOG_WRITE_$$newVelocity$0$_LOG_WRITE_correct (=> (and %lbl%+8719 true) (=> (and
(= _WRITE_HAS_OCCURRED_$$newVelocity$1@0 (ite (and
_P$1
inline$_LOG_WRITE_$$newVelocity$0$track@0) true _WRITE_HAS_OCCURRED_$$newVelocity$1))
(= _WRITE_OFFSET_$$newVelocity$1@0 (ite (and
_P$1
inline$_LOG_WRITE_$$newVelocity$0$track@0) inline$_LOG_WRITE_$$newVelocity$0$_offset$1@0 _WRITE_OFFSET_$$newVelocity$1))
(= _WRITE_SOURCE_$$newVelocity$1@0 (ite (and
_P$1
inline$_LOG_WRITE_$$newVelocity$0$track@0) #x0000000d _WRITE_SOURCE_$$newVelocity$1))
(= (ControlFlow 0 8719) 8805)) $for.cond.tail$9_correct))))
(let ((inline$_LOG_WRITE_$$newVelocity$0$Entry_correct (=> (and %lbl%+8717 true) (=> (and
(= inline$_LOG_WRITE_$$newVelocity$0$_offset$1@0 (bvmul v1$1@0 #x00000004))
(= (ControlFlow 0 8717) 8719)) inline$_LOG_WRITE_$$newVelocity$0$_LOG_WRITE_correct))))
(let (($for.cond.tail$8_correct (=> (and %lbl%+8723 true) (=> (= call3604formal@_offset$2@0 (bvadd (bvmul v1$2@0 #x00000004) #x00000003)) (and
(or %lbl%@29564 (=> (= (ControlFlow 0 8723) (- 0 29564)) (not (and
_P$2
_WRITE_HAS_OCCURRED_$$newPosition$1@3
(= _WRITE_OFFSET_$$newPosition$1@3 call3604formal@_offset$2@0)))))
(=> (not (and
_P$2
_WRITE_HAS_OCCURRED_$$newPosition$1@3
(= _WRITE_OFFSET_$$newPosition$1@3 call3604formal@_offset$2@0))) (and
(or %lbl%@29576 (=> (= (ControlFlow 0 8723) (- 0 29576)) (not (and
_P$2
_READ_HAS_OCCURRED_$$newPosition$1
(= _READ_OFFSET_$$newPosition$1 call3604formal@_offset$2@0)))))
(=> (not (and
_P$2
_READ_HAS_OCCURRED_$$newPosition$1
(= _READ_OFFSET_$$newPosition$1 call3604formal@_offset$2@0))) (and
(or %lbl%@29590 (=> (= (ControlFlow 0 8723) (- 0 29590)) (=> _P$1 true)))
(=> (=> _P$1 true) (=> (= (ControlFlow 0 8723) 8717) inline$_LOG_WRITE_$$newVelocity$0$Entry_correct)))))))))))
(let ((inline$_LOG_WRITE_$$newPosition$3$_LOG_WRITE_correct (=> (and %lbl%+8637 true) (=> (and
(= _WRITE_HAS_OCCURRED_$$newPosition$1@3 (ite (and
_P$1
inline$_LOG_WRITE_$$newPosition$3$track@0) true _WRITE_HAS_OCCURRED_$$newPosition$1@2))
(= _WRITE_OFFSET_$$newPosition$1@3 (ite (and
_P$1
inline$_LOG_WRITE_$$newPosition$3$track@0) inline$_LOG_WRITE_$$newPosition$3$_offset$1@0 _WRITE_OFFSET_$$newPosition$1@2))
(= _WRITE_SOURCE_$$newPosition$1@3 (ite (and
_P$1
inline$_LOG_WRITE_$$newPosition$3$track@0) #x0000000c _WRITE_SOURCE_$$newPosition$1@2))
(= (ControlFlow 0 8637) 8723)) $for.cond.tail$8_correct))))
(let ((inline$_LOG_WRITE_$$newPosition$3$Entry_correct (=> (and %lbl%+8635 true) (=> (and
(= inline$_LOG_WRITE_$$newPosition$3$_offset$1@0 (bvadd (bvmul v1$1@0 #x00000004) #x00000003))
(= (ControlFlow 0 8635) 8637)) inline$_LOG_WRITE_$$newPosition$3$_LOG_WRITE_correct))))
(let (($for.cond.tail$7_correct (=> (and %lbl%+8641 true) (=> (= call3567formal@_offset$2@0 (bvadd (bvmul v1$2@0 #x00000004) #x00000002)) (and
(or %lbl%@29441 (=> (= (ControlFlow 0 8641) (- 0 29441)) (not (and
_P$2
_WRITE_HAS_OCCURRED_$$newPosition$1@2
(= _WRITE_OFFSET_$$newPosition$1@2 call3567formal@_offset$2@0)))))
(=> (not (and
_P$2
_WRITE_HAS_OCCURRED_$$newPosition$1@2
(= _WRITE_OFFSET_$$newPosition$1@2 call3567formal@_offset$2@0))) (and
(or %lbl%@29453 (=> (= (ControlFlow 0 8641) (- 0 29453)) (not (and
_P$2
_READ_HAS_OCCURRED_$$newPosition$1
(= _READ_OFFSET_$$newPosition$1 call3567formal@_offset$2@0)))))
(=> (not (and
_P$2
_READ_HAS_OCCURRED_$$newPosition$1
(= _READ_OFFSET_$$newPosition$1 call3567formal@_offset$2@0))) (and
(or %lbl%@29467 (=> (= (ControlFlow 0 8641) (- 0 29467)) (=> _P$1 true)))
(=> (=> _P$1 true) (=> (= (ControlFlow 0 8641) 8635) inline$_LOG_WRITE_$$newPosition$3$Entry_correct)))))))))))
(let ((inline$_LOG_WRITE_$$newPosition$2$_LOG_WRITE_correct (=> (and %lbl%+8555 true) (=> (and
(= _WRITE_HAS_OCCURRED_$$newPosition$1@2 (ite (and
_P$1
inline$_LOG_WRITE_$$newPosition$2$track@0) true _WRITE_HAS_OCCURRED_$$newPosition$1@1))
(= _WRITE_OFFSET_$$newPosition$1@2 (ite (and
_P$1
inline$_LOG_WRITE_$$newPosition$2$track@0) inline$_LOG_WRITE_$$newPosition$2$_offset$1@0 _WRITE_OFFSET_$$newPosition$1@1))
(= _WRITE_SOURCE_$$newPosition$1@2 (ite (and
_P$1
inline$_LOG_WRITE_$$newPosition$2$track@0) #x0000000b _WRITE_SOURCE_$$newPosition$1@1))
(= (ControlFlow 0 8555) 8641)) $for.cond.tail$7_correct))))
(let ((inline$_LOG_WRITE_$$newPosition$2$Entry_correct (=> (and %lbl%+8553 true) (=> (and
(= inline$_LOG_WRITE_$$newPosition$2$_offset$1@0 (bvadd (bvmul v1$1@0 #x00000004) #x00000002))
(= (ControlFlow 0 8553) 8555)) inline$_LOG_WRITE_$$newPosition$2$_LOG_WRITE_correct))))
(let (($for.cond.tail$6_correct (=> (and %lbl%+8559 true) (=> (= call3530formal@_offset$2@0 (bvadd (bvmul v1$2@0 #x00000004) #x00000001)) (and
(or %lbl%@29318 (=> (= (ControlFlow 0 8559) (- 0 29318)) (not (and
_P$2
_WRITE_HAS_OCCURRED_$$newPosition$1@1
(= _WRITE_OFFSET_$$newPosition$1@1 call3530formal@_offset$2@0)))))
(=> (not (and
_P$2
_WRITE_HAS_OCCURRED_$$newPosition$1@1
(= _WRITE_OFFSET_$$newPosition$1@1 call3530formal@_offset$2@0))) (and
(or %lbl%@29330 (=> (= (ControlFlow 0 8559) (- 0 29330)) (not (and
_P$2
_READ_HAS_OCCURRED_$$newPosition$1
(= _READ_OFFSET_$$newPosition$1 call3530formal@_offset$2@0)))))
(=> (not (and
_P$2
_READ_HAS_OCCURRED_$$newPosition$1
(= _READ_OFFSET_$$newPosition$1 call3530formal@_offset$2@0))) (and
(or %lbl%@29344 (=> (= (ControlFlow 0 8559) (- 0 29344)) (=> _P$1 true)))
(=> (=> _P$1 true) (=> (= (ControlFlow 0 8559) 8553) inline$_LOG_WRITE_$$newPosition$2$Entry_correct)))))))))))
(let ((inline$_LOG_WRITE_$$newPosition$1$_LOG_WRITE_correct (=> (and %lbl%+8473 true) (=> (and
(= _WRITE_HAS_OCCURRED_$$newPosition$1@1 (ite (and
_P$1
inline$_LOG_WRITE_$$newPosition$1$track@0) true _WRITE_HAS_OCCURRED_$$newPosition$1@0))
(= _WRITE_OFFSET_$$newPosition$1@1 (ite (and
_P$1
inline$_LOG_WRITE_$$newPosition$1$track@0) inline$_LOG_WRITE_$$newPosition$1$_offset$1@0 _WRITE_OFFSET_$$newPosition$1@0))
(= _WRITE_SOURCE_$$newPosition$1@1 (ite (and
_P$1
inline$_LOG_WRITE_$$newPosition$1$track@0) #x0000000a _WRITE_SOURCE_$$newPosition$1@0))
(= (ControlFlow 0 8473) 8559)) $for.cond.tail$6_correct))))
(let ((inline$_LOG_WRITE_$$newPosition$1$Entry_correct (=> (and %lbl%+8471 true) (=> (and
(= inline$_LOG_WRITE_$$newPosition$1$_offset$1@0 (bvadd (bvmul v1$1@0 #x00000004) #x00000001))
(= (ControlFlow 0 8471) 8473)) inline$_LOG_WRITE_$$newPosition$1$_LOG_WRITE_correct))))
(let (($for.cond.tail$5_correct (=> (and %lbl%+8477 true) (=> (= call3493formal@_offset$2@0 (bvmul v1$2@0 #x00000004)) (and
(or %lbl%@29195 (=> (= (ControlFlow 0 8477) (- 0 29195)) (not (and
_P$2
_WRITE_HAS_OCCURRED_$$newPosition$1@0
(= _WRITE_OFFSET_$$newPosition$1@0 call3493formal@_offset$2@0)))))
(=> (not (and
_P$2
_WRITE_HAS_OCCURRED_$$newPosition$1@0
(= _WRITE_OFFSET_$$newPosition$1@0 call3493formal@_offset$2@0))) (and
(or %lbl%@29207 (=> (= (ControlFlow 0 8477) (- 0 29207)) (not (and
_P$2
_READ_HAS_OCCURRED_$$newPosition$1
(= _READ_OFFSET_$$newPosition$1 call3493formal@_offset$2@0)))))
(=> (not (and
_P$2
_READ_HAS_OCCURRED_$$newPosition$1
(= _READ_OFFSET_$$newPosition$1 call3493formal@_offset$2@0))) (and
(or %lbl%@29221 (=> (= (ControlFlow 0 8477) (- 0 29221)) (=> _P$1 true)))
(=> (=> _P$1 true) (=> (= (ControlFlow 0 8477) 8471) inline$_LOG_WRITE_$$newPosition$1$Entry_correct)))))))))))
(let ((inline$_LOG_WRITE_$$newPosition$0$_LOG_WRITE_correct (=> (and %lbl%+8391 true) (=> (and
(= _WRITE_HAS_OCCURRED_$$newPosition$1@0 (ite (and
_P$1
inline$_LOG_WRITE_$$newPosition$0$track@0) true _WRITE_HAS_OCCURRED_$$newPosition$1))
(= _WRITE_OFFSET_$$newPosition$1@0 (ite (and
_P$1
inline$_LOG_WRITE_$$newPosition$0$track@0) inline$_LOG_WRITE_$$newPosition$0$_offset$1@0 _WRITE_OFFSET_$$newPosition$1))
(= _WRITE_SOURCE_$$newPosition$1@0 (ite (and
_P$1
inline$_LOG_WRITE_$$newPosition$0$track@0) #x00000009 _WRITE_SOURCE_$$newPosition$1))
(= (ControlFlow 0 8391) 8477)) $for.cond.tail$5_correct))))
(let ((inline$_LOG_WRITE_$$newPosition$0$Entry_correct (=> (and %lbl%+8389 true) (=> (and
(= inline$_LOG_WRITE_$$newPosition$0$_offset$1@0 (bvmul v1$1@0 #x00000004))
(= (ControlFlow 0 8389) 8391)) inline$_LOG_WRITE_$$newPosition$0$_LOG_WRITE_correct))))
(let (($for.cond.tail$4_correct (=> (and %lbl%+8395 true) (=> (= call3462formal@_offset$2@0 (bvadd (bvmul v1$2@0 #x00000004) #x00000003)) (and
(or %lbl%@29086 (=> (= (ControlFlow 0 8395) (- 0 29086)) (not (and
_P$2
_WRITE_HAS_OCCURRED_$$vel$1
(= _WRITE_OFFSET_$$vel$1 call3462formal@_offset$2@0)))))
(=> (not (and
_P$2
_WRITE_HAS_OCCURRED_$$vel$1
(= _WRITE_OFFSET_$$vel$1 call3462formal@_offset$2@0))) (and
(or %lbl%@29100 (=> (= (ControlFlow 0 8395) (- 0 29100)) (=> _P$1 true)))
(=> (=> _P$1 true) (=> (= (ControlFlow 0 8395) 8389) inline$_LOG_WRITE_$$newPosition$0$Entry_correct)))))))))
(let ((inline$_LOG_READ_$$vel$3$_LOG_READ_correct (=> (and %lbl%+8309 true) (=> (and
(= _READ_HAS_OCCURRED_$$vel$1@3 (ite (and
_P$1
inline$_LOG_READ_$$vel$3$track@0) true _READ_HAS_OCCURRED_$$vel$1@2))
(= _READ_OFFSET_$$vel$1@3 (ite (and
_P$1
inline$_LOG_READ_$$vel$3$track@0) inline$_LOG_READ_$$vel$3$_offset$1@0 _READ_OFFSET_$$vel$1@2))
(= _READ_SOURCE_$$vel$1@3 (ite (and
_P$1
inline$_LOG_READ_$$vel$3$track@0) #x00000008 _READ_SOURCE_$$vel$1@2))
(= (ControlFlow 0 8309) 8395)) $for.cond.tail$4_correct))))
(let ((inline$_LOG_READ_$$vel$3$Entry_correct (=> (and %lbl%+8307 true) (=> (and
(= inline$_LOG_READ_$$vel$3$_offset$1@0 (bvadd (bvmul v1$1@0 #x00000004) #x00000003))
(= (ControlFlow 0 8307) 8309)) inline$_LOG_READ_$$vel$3$_LOG_READ_correct))))
(let (($for.cond.tail$3_correct (=> (and %lbl%+8313 true) (=> (= call3409formal@_offset$2@0 (bvadd (bvmul v1$2@0 #x00000004) #x00000002)) (and
(or %lbl%@28944 (=> (= (ControlFlow 0 8313) (- 0 28944)) (not (and
_P$2
_WRITE_HAS_OCCURRED_$$vel$1
(= _WRITE_OFFSET_$$vel$1 call3409formal@_offset$2@0)))))
(=> (not (and
_P$2
_WRITE_HAS_OCCURRED_$$vel$1
(= _WRITE_OFFSET_$$vel$1 call3409formal@_offset$2@0))) (and
(or %lbl%@28958 (=> (= (ControlFlow 0 8313) (- 0 28958)) (=> _P$1 true)))
(=> (=> _P$1 true) (=> (and
(= v26$1@0 (ite _P$1 _HAVOC_bv32$1@18 v26$1))
(= v26$2@0 (ite _P$2 _HAVOC_bv32$2@18 v26$2))
(= (ControlFlow 0 8313) 8307)) inline$_LOG_READ_$$vel$3$Entry_correct)))))))))
(let ((inline$_LOG_READ_$$vel$2$_LOG_READ_correct (=> (and %lbl%+8227 true) (=> (and
(= _READ_HAS_OCCURRED_$$vel$1@2 (ite (and
_P$1
inline$_LOG_READ_$$vel$2$track@0) true _READ_HAS_OCCURRED_$$vel$1@1))
(= _READ_OFFSET_$$vel$1@2 (ite (and
_P$1
inline$_LOG_READ_$$vel$2$track@0) inline$_LOG_READ_$$vel$2$_offset$1@0 _READ_OFFSET_$$vel$1@1))
(= _READ_SOURCE_$$vel$1@2 (ite (and
_P$1
inline$_LOG_READ_$$vel$2$track@0) #x00000007 _READ_SOURCE_$$vel$1@1))
(= (ControlFlow 0 8227) 8313)) $for.cond.tail$3_correct))))
(let ((inline$_LOG_READ_$$vel$2$Entry_correct (=> (and %lbl%+8225 true) (=> (and
(= inline$_LOG_READ_$$vel$2$_offset$1@0 (bvadd (bvmul v1$1@0 #x00000004) #x00000002))
(= (ControlFlow 0 8225) 8227)) inline$_LOG_READ_$$vel$2$_LOG_READ_correct))))
(let (($for.cond.tail$2_correct (=> (and %lbl%+8231 true) (=> (= call3356formal@_offset$2@0 (bvadd (bvmul v1$2@0 #x00000004) #x00000001)) (and
(or %lbl%@28802 (=> (= (ControlFlow 0 8231) (- 0 28802)) (not (and
_P$2
_WRITE_HAS_OCCURRED_$$vel$1
(= _WRITE_OFFSET_$$vel$1 call3356formal@_offset$2@0)))))
(=> (not (and
_P$2
_WRITE_HAS_OCCURRED_$$vel$1
(= _WRITE_OFFSET_$$vel$1 call3356formal@_offset$2@0))) (and
(or %lbl%@28816 (=> (= (ControlFlow 0 8231) (- 0 28816)) (=> _P$1 true)))
(=> (=> _P$1 true) (=> (and
(= v25$1@0 (ite _P$1 _HAVOC_bv32$1@17 v25$1))
(= v25$2@0 (ite _P$2 _HAVOC_bv32$2@17 v25$2))
(= (ControlFlow 0 8231) 8225)) inline$_LOG_READ_$$vel$2$Entry_correct)))))))))
(let ((inline$_LOG_READ_$$vel$1$_LOG_READ_correct (=> (and %lbl%+8145 true) (=> (and
(= _READ_HAS_OCCURRED_$$vel$1@1 (ite (and
_P$1
inline$_LOG_READ_$$vel$1$track@0) true _READ_HAS_OCCURRED_$$vel$1@0))
(= _READ_OFFSET_$$vel$1@1 (ite (and
_P$1
inline$_LOG_READ_$$vel$1$track@0) inline$_LOG_READ_$$vel$1$_offset$1@0 _READ_OFFSET_$$vel$1@0))
(= _READ_SOURCE_$$vel$1@1 (ite (and
_P$1
inline$_LOG_READ_$$vel$1$track@0) #x00000006 _READ_SOURCE_$$vel$1@0))
(= (ControlFlow 0 8145) 8231)) $for.cond.tail$2_correct))))
(let ((inline$_LOG_READ_$$vel$1$Entry_correct (=> (and %lbl%+8143 true) (=> (and
(= inline$_LOG_READ_$$vel$1$_offset$1@0 (bvadd (bvmul v1$1@0 #x00000004) #x00000001))
(= (ControlFlow 0 8143) 8145)) inline$_LOG_READ_$$vel$1$_LOG_READ_correct))))
(let (($for.cond.tail$1_correct (=> (and %lbl%+8149 true) (=> (= call3303formal@_offset$2@0 (bvmul v1$2@0 #x00000004)) (and
(or %lbl%@28660 (=> (= (ControlFlow 0 8149) (- 0 28660)) (not (and
_P$2
_WRITE_HAS_OCCURRED_$$vel$1
(= _WRITE_OFFSET_$$vel$1 call3303formal@_offset$2@0)))))
(=> (not (and
_P$2
_WRITE_HAS_OCCURRED_$$vel$1
(= _WRITE_OFFSET_$$vel$1 call3303formal@_offset$2@0))) (and
(or %lbl%@28674 (=> (= (ControlFlow 0 8149) (- 0 28674)) (=> _P$1 true)))
(=> (=> _P$1 true) (=> (and
(= v24$1@0 (ite _P$1 _HAVOC_bv32$1@16 v24$1))
(= v24$2@0 (ite _P$2 _HAVOC_bv32$2@16 v24$2))
(= (ControlFlow 0 8149) 8143)) inline$_LOG_READ_$$vel$1$Entry_correct)))))))))
(let ((inline$_LOG_READ_$$vel$0$_LOG_READ_correct (=> (and %lbl%+8063 true) (=> (and
(= _READ_HAS_OCCURRED_$$vel$1@0 (ite (and
_P$1
inline$_LOG_READ_$$vel$0$track@0) true _READ_HAS_OCCURRED_$$vel$1))
(= _READ_OFFSET_$$vel$1@0 (ite (and
_P$1
inline$_LOG_READ_$$vel$0$track@0) inline$_LOG_READ_$$vel$0$_offset$1@0 _READ_OFFSET_$$vel$1))
(= _READ_SOURCE_$$vel$1@0 (ite (and
_P$1
inline$_LOG_READ_$$vel$0$track@0) #x00000005 _READ_SOURCE_$$vel$1))
(= (ControlFlow 0 8063) 8149)) $for.cond.tail$1_correct))))
(let ((inline$_LOG_READ_$$vel$0$Entry_correct (=> (and %lbl%+8061 true) (=> (and
(= inline$_LOG_READ_$$vel$0$_offset$1@0 (bvmul v1$1@0 #x00000004))
(= (ControlFlow 0 8061) 8063)) inline$_LOG_READ_$$vel$0$_LOG_READ_correct))))
(let (($for.cond.tail_correct (=> (and %lbl%+8067 true) (=> (and
(not p0$1@3)
(not p0$2@3)) (and
(or %lbl%@28534 (=> (= (ControlFlow 0 8067) (- 0 28534)) (=> _P$1 true)))
(=> (=> _P$1 true) (=> (and
(= v23$1@0 (ite _P$1 _HAVOC_bv32$1@15 v23$1))
(= v23$2@0 (ite _P$2 _HAVOC_bv32$2@15 v23$2))
(= (ControlFlow 0 8067) 8061)) inline$_LOG_READ_$$vel$0$Entry_correct)))))))
(let (($for.cond.backedge_correct (=> (and %lbl%+8973 true) (=> (or
p0$1@3
p0$2@3) (and
(or %lbl%@27591 (=> (= (ControlFlow 0 8973) (- 0 27591)) (=> _b10 (=> _WRITE_HAS_OCCURRED_$$localPos$1@4 (or
(= _WRITE_OFFSET_$$localPos$1@4 (bvmul local_id_x$1 #x00000004))
(= _WRITE_OFFSET_$$localPos$1@4 (bvadd (bvmul local_id_x$1 #x00000004) #x00000001))
(= _WRITE_OFFSET_$$localPos$1@4 (bvadd (bvmul local_id_x$1 #x00000004) #x00000002))
(= _WRITE_OFFSET_$$localPos$1@4 (bvadd (bvmul local_id_x$1 #x00000004) #x00000003)))))))
(=> (=> _b10 (=> _WRITE_HAS_OCCURRED_$$localPos$1@4 (or
(= _WRITE_OFFSET_$$localPos$1@4 (bvmul local_id_x$1 #x00000004))
(= _WRITE_OFFSET_$$localPos$1@4 (bvadd (bvmul local_id_x$1 #x00000004) #x00000001))
(= _WRITE_OFFSET_$$localPos$1@4 (bvadd (bvmul local_id_x$1 #x00000004) #x00000002))
(= _WRITE_OFFSET_$$localPos$1@4 (bvadd (bvmul local_id_x$1 #x00000004) #x00000003))))) (and
(or %lbl%@27652 (=> (= (ControlFlow 0 8973) (- 0 27652)) (=> _b9 (=> _READ_HAS_OCCURRED_$$localPos$1@6 (or
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvmul #x00000000 #x00000004)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000001)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000002)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003))))))))
(=> (=> _b9 (=> _READ_HAS_OCCURRED_$$localPos$1@6 (or
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvmul #x00000000 #x00000004)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000001)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000002)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003)))))) (and
(or %lbl%@27848 (=> (= (ControlFlow 0 8973) (- 0 27848)) (=> _b8 (not _WRITE_HAS_OCCURRED_$$localPos$1@4))))
(=> (=> _b8 (not _WRITE_HAS_OCCURRED_$$localPos$1@4)) (and
(or %lbl%@27855 (=> (= (ControlFlow 0 8973) (- 0 27855)) (=> _b7 (not _READ_HAS_OCCURRED_$$localPos$1@6))))
(=> (=> _b7 (not _READ_HAS_OCCURRED_$$localPos$1@6)) (and
(or %lbl%@27862 (=> (= (ControlFlow 0 8973) (- 0 27862)) (=> _b6 (=> _READ_HAS_OCCURRED_$$pos$1@8 (or
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@8) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004)))
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@8) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvadd (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004) #x00000001)))
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@8) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvadd (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004) #x00000002)))
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@8) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvadd (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004) #x00000003))))))))
(=> (=> _b6 (=> _READ_HAS_OCCURRED_$$pos$1@8 (or
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@8) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004)))
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@8) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvadd (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004) #x00000001)))
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@8) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvadd (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004) #x00000002)))
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@8) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvadd (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004) #x00000003)))))) (and
(or %lbl%@28083 (=> (= (ControlFlow 0 8973) (- 0 28083)) (=> _b5 (not _READ_HAS_OCCURRED_$$pos$1@8))))
(=> (=> _b5 (not _READ_HAS_OCCURRED_$$pos$1@8)) (and
(or %lbl%@28090 (=> (= (ControlFlow 0 8973) (- 0 28090)) (=> _b4 (=> (and
p0$1@3
p0$2@3) (= $j.0$1@3 $j.0$2@3)))))
(=> (=> _b4 (=> (and
p0$1@3
p0$2@3) (= $j.0$1@3 $j.0$2@3))) (and
(or %lbl%@28104 (=> (= (ControlFlow 0 8973) (- 0 28104)) (=> _b3 (=> (and
p0$1@3
p0$2@3) (= $acc.1$1@3 $acc.1$2@3)))))
(=> (=> _b3 (=> (and
p0$1@3
p0$2@3) (= $acc.1$1@3 $acc.1$2@3))) (and
(or %lbl%@28118 (=> (= (ControlFlow 0 8973) (- 0 28118)) (=> _b2 (=> (and
p0$1@3
p0$2@3) (= $i.0$1@2 $i.0$2@2)))))
(=> (=> _b2 (=> (and
p0$1@3
p0$2@3) (= $i.0$1@2 $i.0$2@2))) (and
(or %lbl%@28132 (=> (= (ControlFlow 0 8973) (- 0 28132)) (=> _b1 (=> (and
p0$1@3
p0$2@3) (= $acc.0$1@2 $acc.0$2@2)))))
(=> (=> _b1 (=> (and
p0$1@3
p0$2@3) (= $acc.0$1@2 $acc.0$2@2))) (and
(or %lbl%@28146 (=> (= (ControlFlow 0 8973) (- 0 28146)) (=> _b0 (= p0$1@3 p0$2@3))))
(=> (=> _b0 (= p0$1@3 p0$2@3)) (and
(or %lbl%@28154 (=> (= (ControlFlow 0 8973) (- 0 28154)) (=> _READ_HAS_OCCURRED_$$vel$1 (or
(= _READ_SOURCE_$$vel$1 #x00000005)
(= _READ_SOURCE_$$vel$1 #x00000006)
(= _READ_SOURCE_$$vel$1 #x00000007)
(= _READ_SOURCE_$$vel$1 #x00000008)))))
(=> (=> _READ_HAS_OCCURRED_$$vel$1 (or
(= _READ_SOURCE_$$vel$1 #x00000005)
(= _READ_SOURCE_$$vel$1 #x00000006)
(= _READ_SOURCE_$$vel$1 #x00000007)
(= _READ_SOURCE_$$vel$1 #x00000008))) (and
(or %lbl%@28188 (=> (= (ControlFlow 0 8973) (- 0 28188)) (=> _WRITE_HAS_OCCURRED_$$vel$1 false)))
(=> (=> _WRITE_HAS_OCCURRED_$$vel$1 false) (and
(or %lbl%@28194 (=> (= (ControlFlow 0 8973) (- 0 28194)) (=> (not _READ_HAS_OCCURRED_$$vel$1) (= _READ_SOURCE_$$vel$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$vel$1) (= _READ_SOURCE_$$vel$1 #x00000000)) (and
(or %lbl%@28206 (=> (= (ControlFlow 0 8973) (- 0 28206)) (=> (not _WRITE_HAS_OCCURRED_$$vel$1) (= _WRITE_SOURCE_$$vel$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$vel$1) (= _WRITE_SOURCE_$$vel$1 #x00000000)) (and
(or %lbl%@28218 (=> (= (ControlFlow 0 8973) (- 0 28218)) (=> _READ_HAS_OCCURRED_$$pos$1@8 (or
(= _READ_SOURCE_$$pos$1@8 #x00000001)
(= _READ_SOURCE_$$pos$1@8 #x00000002)
(= _READ_SOURCE_$$pos$1@8 #x00000003)
(= _READ_SOURCE_$$pos$1@8 #x00000004)
(= _READ_SOURCE_$$pos$1@8 #x00000011)
(= _READ_SOURCE_$$pos$1@8 #x00000012)
(= _READ_SOURCE_$$pos$1@8 #x00000013)
(= _READ_SOURCE_$$pos$1@8 #x00000014)))))
(=> (=> _READ_HAS_OCCURRED_$$pos$1@8 (or
(= _READ_SOURCE_$$pos$1@8 #x00000001)
(= _READ_SOURCE_$$pos$1@8 #x00000002)
(= _READ_SOURCE_$$pos$1@8 #x00000003)
(= _READ_SOURCE_$$pos$1@8 #x00000004)
(= _READ_SOURCE_$$pos$1@8 #x00000011)
(= _READ_SOURCE_$$pos$1@8 #x00000012)
(= _READ_SOURCE_$$pos$1@8 #x00000013)
(= _READ_SOURCE_$$pos$1@8 #x00000014))) (and
(or %lbl%@28275 (=> (= (ControlFlow 0 8973) (- 0 28275)) (=> _WRITE_HAS_OCCURRED_$$pos$1 false)))
(=> (=> _WRITE_HAS_OCCURRED_$$pos$1 false) (and
(or %lbl%@28281 (=> (= (ControlFlow 0 8973) (- 0 28281)) (=> (not _READ_HAS_OCCURRED_$$pos$1@8) (= _READ_SOURCE_$$pos$1@8 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$pos$1@8) (= _READ_SOURCE_$$pos$1@8 #x00000000)) (and
(or %lbl%@28291 (=> (= (ControlFlow 0 8973) (- 0 28291)) (=> (not _WRITE_HAS_OCCURRED_$$pos$1) (= _WRITE_SOURCE_$$pos$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$pos$1) (= _WRITE_SOURCE_$$pos$1 #x00000000)) (and
(or %lbl%@28303 (=> (= (ControlFlow 0 8973) (- 0 28303)) (=> _READ_HAS_OCCURRED_$$localPos$1@6 (or
(= _READ_SOURCE_$$localPos$1@6 #x00000019)
(= _READ_SOURCE_$$localPos$1@6 #x0000001a)
(= _READ_SOURCE_$$localPos$1@6 #x0000001b)
(= _READ_SOURCE_$$localPos$1@6 #x0000001c)
(= _READ_SOURCE_$$localPos$1@6 #x0000001d)))))
(=> (=> _READ_HAS_OCCURRED_$$localPos$1@6 (or
(= _READ_SOURCE_$$localPos$1@6 #x00000019)
(= _READ_SOURCE_$$localPos$1@6 #x0000001a)
(= _READ_SOURCE_$$localPos$1@6 #x0000001b)
(= _READ_SOURCE_$$localPos$1@6 #x0000001c)
(= _READ_SOURCE_$$localPos$1@6 #x0000001d))) (and
(or %lbl%@28339 (=> (= (ControlFlow 0 8973) (- 0 28339)) (=> _WRITE_HAS_OCCURRED_$$localPos$1@4 (or
(= _WRITE_SOURCE_$$localPos$1@4 #x00000015)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000016)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000017)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000018)))))
(=> (=> _WRITE_HAS_OCCURRED_$$localPos$1@4 (or
(= _WRITE_SOURCE_$$localPos$1@4 #x00000015)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000016)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000017)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000018))) (and
(or %lbl%@28368 (=> (= (ControlFlow 0 8973) (- 0 28368)) (=> (not _READ_HAS_OCCURRED_$$localPos$1@6) (= _READ_SOURCE_$$localPos$1@6 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$localPos$1@6) (= _READ_SOURCE_$$localPos$1@6 #x00000000)) (and
(or %lbl%@28378 (=> (= (ControlFlow 0 8973) (- 0 28378)) (=> (not _WRITE_HAS_OCCURRED_$$localPos$1@4) (= _WRITE_SOURCE_$$localPos$1@4 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$localPos$1@4) (= _WRITE_SOURCE_$$localPos$1@4 #x00000000)) (and
(or %lbl%@28388 (=> (= (ControlFlow 0 8973) (- 0 28388)) (=> _READ_HAS_OCCURRED_$$newVelocity$1 false)))
(=> (=> _READ_HAS_OCCURRED_$$newVelocity$1 false) (and
(or %lbl%@28394 (=> (= (ControlFlow 0 8973) (- 0 28394)) (=> _WRITE_HAS_OCCURRED_$$newVelocity$1 (or
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000d)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000e)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000f)
(= _WRITE_SOURCE_$$newVelocity$1 #x00000010)))))
(=> (=> _WRITE_HAS_OCCURRED_$$newVelocity$1 (or
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000d)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000e)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000f)
(= _WRITE_SOURCE_$$newVelocity$1 #x00000010))) (and
(or %lbl%@28428 (=> (= (ControlFlow 0 8973) (- 0 28428)) (=> (not _READ_HAS_OCCURRED_$$newVelocity$1) (= _READ_SOURCE_$$newVelocity$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$newVelocity$1) (= _READ_SOURCE_$$newVelocity$1 #x00000000)) (and
(or %lbl%@28440 (=> (= (ControlFlow 0 8973) (- 0 28440)) (=> (not _WRITE_HAS_OCCURRED_$$newVelocity$1) (= _WRITE_SOURCE_$$newVelocity$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$newVelocity$1) (= _WRITE_SOURCE_$$newVelocity$1 #x00000000)) (and
(or %lbl%@28452 (=> (= (ControlFlow 0 8973) (- 0 28452)) (=> _READ_HAS_OCCURRED_$$newPosition$1 false)))
(=> (=> _READ_HAS_OCCURRED_$$newPosition$1 false) (and
(or %lbl%@28458 (=> (= (ControlFlow 0 8973) (- 0 28458)) (=> _WRITE_HAS_OCCURRED_$$newPosition$1 (or
(= _WRITE_SOURCE_$$newPosition$1 #x00000009)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000a)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000b)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000c)))))
(=> (=> _WRITE_HAS_OCCURRED_$$newPosition$1 (or
(= _WRITE_SOURCE_$$newPosition$1 #x00000009)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000a)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000b)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000c))) (and
(or %lbl%@28492 (=> (= (ControlFlow 0 8973) (- 0 28492)) (=> (not _READ_HAS_OCCURRED_$$newPosition$1) (= _READ_SOURCE_$$newPosition$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$newPosition$1) (= _READ_SOURCE_$$newPosition$1 #x00000000)) (and
(or %lbl%@28504 (=> (= (ControlFlow 0 8973) (- 0 28504)) (=> (not _WRITE_HAS_OCCURRED_$$newPosition$1) (= _WRITE_SOURCE_$$newPosition$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$newPosition$1) (= _WRITE_SOURCE_$$newPosition$1 #x00000000)) (and
(or %lbl%@28516 (=> (= (ControlFlow 0 8973) (- 0 28516)) (=> p0$1@3 _P$1)))
(=> (=> p0$1@3 _P$1) (and
(or %lbl%@28521 (=> (= (ControlFlow 0 8973) (- 0 28521)) (=> p0$2@3 _P$2)))
(=> (=> p0$2@3 _P$2) true))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(let (($for.cond5.tail$1_correct (=> (and %lbl%+7985 true) (=> (and
(= $acc.0$1@2 (ite p1$1@1 $acc.1$1@3 $acc.0$1@1))
(= $acc.0$2@2 (ite p1$2@1 $acc.1$2@3 $acc.0$2@1))
(= $i.0$1@2 (ite p1$1@1 (bvadd $i.0$1@1 #x00000001) $i.0$1@1))
(= $i.0$2@2 (ite p1$2@1 (bvadd $i.0$2@1 #x00000001) $i.0$2@1))
(= p0$1@3 (ite p1$1@1 true p0$1@2))
(= p0$2@3 (ite p1$2@1 true p0$2@2))) (and
(=> (= (ControlFlow 0 7985) 8973) $for.cond.backedge_correct)
(=> (= (ControlFlow 0 7985) 8067) $for.cond.tail_correct))))))
(let ((inline$$bugle_barrier$1$Return_correct (=> (and %lbl%+7981 true) (=> (= (ControlFlow 0 7981) 7985) $for.cond5.tail$1_correct))))
(let ((inline$$bugle_barrier$1$anon18_Else_correct (=> (and %lbl%+7969 true) (=> (and
(not (and
p1$2@1
(= inline$$bugle_barrier$1$$1$2@1 #b1)))
(= (ControlFlow 0 7969) 7981)) inline$$bugle_barrier$1$Return_correct))))
(let ((inline$$bugle_barrier$1$anon18_Then_correct (=> (and %lbl%+7971 true) (=> (and
p1$2@1
(= inline$$bugle_barrier$1$$1$2@1 #b1)
(= (ControlFlow 0 7971) 7981)) inline$$bugle_barrier$1$Return_correct))))
(let ((inline$$bugle_barrier$1$anon9_correct (=> (and %lbl%+7967 true) (and
(=> (= (ControlFlow 0 7967) 7971) inline$$bugle_barrier$1$anon18_Then_correct)
(=> (= (ControlFlow 0 7967) 7969) inline$$bugle_barrier$1$anon18_Else_correct)))))
(let ((inline$$bugle_barrier$1$anon17_Else_correct (=> (and %lbl%+7965 true) (=> (and
(not (and
p1$1@1
(= inline$$bugle_barrier$1$$1$1@1 #b1)))
(= (ControlFlow 0 7965) 7967)) inline$$bugle_barrier$1$anon9_correct))))
(let ((inline$$bugle_barrier$1$anon17_Then_correct (=> (and %lbl%+7973 true) (=> (and
p1$1@1
(= inline$$bugle_barrier$1$$1$1@1 #b1)) (=> (and
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _READ_HAS_OCCURRED_$$pos$1@8))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _WRITE_HAS_OCCURRED_$$pos$1))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _READ_HAS_OCCURRED_$$vel$1))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _WRITE_HAS_OCCURRED_$$vel$1))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _READ_HAS_OCCURRED_$$newPosition$1))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _WRITE_HAS_OCCURRED_$$newPosition$1))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _READ_HAS_OCCURRED_$$newVelocity$1))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _WRITE_HAS_OCCURRED_$$newVelocity$1))) (and
(=> (= (ControlFlow 0 7973) 7971) inline$$bugle_barrier$1$anon18_Then_correct)
(=> (= (ControlFlow 0 7973) 7969) inline$$bugle_barrier$1$anon18_Else_correct)))))))
(let ((inline$$bugle_barrier$1$anon4_correct (=> (and %lbl%+7963 true) (and
(=> (= (ControlFlow 0 7963) 7973) inline$$bugle_barrier$1$anon17_Then_correct)
(=> (= (ControlFlow 0 7963) 7965) inline$$bugle_barrier$1$anon17_Else_correct)))))
(let ((inline$$bugle_barrier$1$anon16_Else_correct (=> (and %lbl%+7961 true) (=> (and
(not (and
p1$2@1
(= inline$$bugle_barrier$1$$0$2@1 #b1)))
(= (ControlFlow 0 7961) 7963)) inline$$bugle_barrier$1$anon4_correct))))
(let ((inline$$bugle_barrier$1$anon16_Then_correct (=> (and %lbl%+7975 true) (=> (and
p1$2@1
(= inline$$bugle_barrier$1$$0$2@1 #b1)) (and
(=> (= (ControlFlow 0 7975) 7973) inline$$bugle_barrier$1$anon17_Then_correct)
(=> (= (ControlFlow 0 7975) 7965) inline$$bugle_barrier$1$anon17_Else_correct))))))
(let ((inline$$bugle_barrier$1$anon2_correct (=> (and %lbl%+7959 true) (and
(=> (= (ControlFlow 0 7959) 7975) inline$$bugle_barrier$1$anon16_Then_correct)
(=> (= (ControlFlow 0 7959) 7961) inline$$bugle_barrier$1$anon16_Else_correct)))))
(let ((inline$$bugle_barrier$1$anon15_Else_correct (=> (and %lbl%+7957 true) (=> (and
(not (and
p1$1@1
(= inline$$bugle_barrier$1$$0$1@1 #b1)))
(= (ControlFlow 0 7957) 7959)) inline$$bugle_barrier$1$anon2_correct))))
(let ((inline$$bugle_barrier$1$anon15_Then_correct (=> (and %lbl%+7977 true) (=> (and
p1$1@1
(= inline$$bugle_barrier$1$$0$1@1 #b1)
(not _READ_HAS_OCCURRED_$$localPos$1@6)
(not _WRITE_HAS_OCCURRED_$$localPos$1@4)) (and
(=> (= (ControlFlow 0 7977) 7975) inline$$bugle_barrier$1$anon16_Then_correct)
(=> (= (ControlFlow 0 7977) 7961) inline$$bugle_barrier$1$anon16_Else_correct))))))
(let ((inline$$bugle_barrier$1$anon14_Else_correct (=> (and %lbl%+7955 true) (=> (not (or
(and
(not p1$1@1)
(not p1$2@1))
(and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)
(or
(not p1$1@1)
(not p1$2@1))))) (and
(=> (= (ControlFlow 0 7955) 7977) inline$$bugle_barrier$1$anon15_Then_correct)
(=> (= (ControlFlow 0 7955) 7957) inline$$bugle_barrier$1$anon15_Else_correct))))))
(let ((inline$$bugle_barrier$1$anon14_Then_correct (=> (and %lbl%+7979 true) (=> (and
(or
(and
(not p1$1@1)
(not p1$2@1))
(and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)
(or
(not p1$1@1)
(not p1$2@1))))
(= (ControlFlow 0 7979) 7985)) $for.cond5.tail$1_correct))))
(let ((inline$$bugle_barrier$1$Entry_correct (=> (and %lbl%+7951 true) (=> (and
(= inline$$bugle_barrier$1$$0$1@1 (ite true #b1 #b0))
(= inline$$bugle_barrier$1$$1$1@1 (ite false #b1 #b0))
(= inline$$bugle_barrier$1$$0$2@1 (ite true #b1 #b0))
(= inline$$bugle_barrier$1$$1$2@1 (ite false #b1 #b0))) (and
(or %lbl%@27100 (=> (= (ControlFlow 0 7951) (- 0 27100)) (=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (= p1$1@1 p1$2@1))))
(=> (=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (= p1$1@1 p1$2@1)) (and
(=> (= (ControlFlow 0 7951) 7979) inline$$bugle_barrier$1$anon14_Then_correct)
(=> (= (ControlFlow 0 7951) 7955) inline$$bugle_barrier$1$anon14_Else_correct))))))))
(let (($for.cond5.tail_correct (=> (and %lbl%+7983 true) (=> (not p2$1@4) (=> (and
(not p2$2@4)
(= (ControlFlow 0 7983) 7951)) inline$$bugle_barrier$1$Entry_correct)))))
(let (($for.cond5.backedge_correct (=> (and %lbl%+8975 true) (=> (or
p2$1@4
p2$2@4) (and
(or %lbl%@26466 (=> (= (ControlFlow 0 8975) (- 0 26466)) (=> _b11 (=> _READ_HAS_OCCURRED_$$localPos$1@6 (or
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvmul #x00000000 #x00000004)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000001)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000002)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003))))))))
(=> (=> _b11 (=> _READ_HAS_OCCURRED_$$localPos$1@6 (or
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvmul #x00000000 #x00000004)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000001)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000002)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@6) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003)))))) (and
(or %lbl%@26662 (=> (= (ControlFlow 0 8975) (- 0 26662)) (=> _READ_HAS_OCCURRED_$$vel$1 (or
(= _READ_SOURCE_$$vel$1 #x00000005)
(= _READ_SOURCE_$$vel$1 #x00000006)
(= _READ_SOURCE_$$vel$1 #x00000007)
(= _READ_SOURCE_$$vel$1 #x00000008)))))
(=> (=> _READ_HAS_OCCURRED_$$vel$1 (or
(= _READ_SOURCE_$$vel$1 #x00000005)
(= _READ_SOURCE_$$vel$1 #x00000006)
(= _READ_SOURCE_$$vel$1 #x00000007)
(= _READ_SOURCE_$$vel$1 #x00000008))) (and
(or %lbl%@26696 (=> (= (ControlFlow 0 8975) (- 0 26696)) (=> _WRITE_HAS_OCCURRED_$$vel$1 false)))
(=> (=> _WRITE_HAS_OCCURRED_$$vel$1 false) (and
(or %lbl%@26702 (=> (= (ControlFlow 0 8975) (- 0 26702)) (=> (not _READ_HAS_OCCURRED_$$vel$1) (= _READ_SOURCE_$$vel$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$vel$1) (= _READ_SOURCE_$$vel$1 #x00000000)) (and
(or %lbl%@26714 (=> (= (ControlFlow 0 8975) (- 0 26714)) (=> (not _WRITE_HAS_OCCURRED_$$vel$1) (= _WRITE_SOURCE_$$vel$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$vel$1) (= _WRITE_SOURCE_$$vel$1 #x00000000)) (and
(or %lbl%@26726 (=> (= (ControlFlow 0 8975) (- 0 26726)) (=> _READ_HAS_OCCURRED_$$pos$1@8 (or
(= _READ_SOURCE_$$pos$1@8 #x00000001)
(= _READ_SOURCE_$$pos$1@8 #x00000002)
(= _READ_SOURCE_$$pos$1@8 #x00000003)
(= _READ_SOURCE_$$pos$1@8 #x00000004)
(= _READ_SOURCE_$$pos$1@8 #x00000011)
(= _READ_SOURCE_$$pos$1@8 #x00000012)
(= _READ_SOURCE_$$pos$1@8 #x00000013)
(= _READ_SOURCE_$$pos$1@8 #x00000014)))))
(=> (=> _READ_HAS_OCCURRED_$$pos$1@8 (or
(= _READ_SOURCE_$$pos$1@8 #x00000001)
(= _READ_SOURCE_$$pos$1@8 #x00000002)
(= _READ_SOURCE_$$pos$1@8 #x00000003)
(= _READ_SOURCE_$$pos$1@8 #x00000004)
(= _READ_SOURCE_$$pos$1@8 #x00000011)
(= _READ_SOURCE_$$pos$1@8 #x00000012)
(= _READ_SOURCE_$$pos$1@8 #x00000013)
(= _READ_SOURCE_$$pos$1@8 #x00000014))) (and
(or %lbl%@26783 (=> (= (ControlFlow 0 8975) (- 0 26783)) (=> _WRITE_HAS_OCCURRED_$$pos$1 false)))
(=> (=> _WRITE_HAS_OCCURRED_$$pos$1 false) (and
(or %lbl%@26789 (=> (= (ControlFlow 0 8975) (- 0 26789)) (=> (not _READ_HAS_OCCURRED_$$pos$1@8) (= _READ_SOURCE_$$pos$1@8 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$pos$1@8) (= _READ_SOURCE_$$pos$1@8 #x00000000)) (and
(or %lbl%@26799 (=> (= (ControlFlow 0 8975) (- 0 26799)) (=> (not _WRITE_HAS_OCCURRED_$$pos$1) (= _WRITE_SOURCE_$$pos$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$pos$1) (= _WRITE_SOURCE_$$pos$1 #x00000000)) (and
(or %lbl%@26811 (=> (= (ControlFlow 0 8975) (- 0 26811)) (=> _READ_HAS_OCCURRED_$$localPos$1@6 (or
(= _READ_SOURCE_$$localPos$1@6 #x00000019)
(= _READ_SOURCE_$$localPos$1@6 #x0000001a)
(= _READ_SOURCE_$$localPos$1@6 #x0000001b)
(= _READ_SOURCE_$$localPos$1@6 #x0000001c)
(= _READ_SOURCE_$$localPos$1@6 #x0000001d)))))
(=> (=> _READ_HAS_OCCURRED_$$localPos$1@6 (or
(= _READ_SOURCE_$$localPos$1@6 #x00000019)
(= _READ_SOURCE_$$localPos$1@6 #x0000001a)
(= _READ_SOURCE_$$localPos$1@6 #x0000001b)
(= _READ_SOURCE_$$localPos$1@6 #x0000001c)
(= _READ_SOURCE_$$localPos$1@6 #x0000001d))) (and
(or %lbl%@26847 (=> (= (ControlFlow 0 8975) (- 0 26847)) (=> _WRITE_HAS_OCCURRED_$$localPos$1@4 (or
(= _WRITE_SOURCE_$$localPos$1@4 #x00000015)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000016)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000017)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000018)))))
(=> (=> _WRITE_HAS_OCCURRED_$$localPos$1@4 (or
(= _WRITE_SOURCE_$$localPos$1@4 #x00000015)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000016)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000017)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000018))) (and
(or %lbl%@26876 (=> (= (ControlFlow 0 8975) (- 0 26876)) (=> (not _READ_HAS_OCCURRED_$$localPos$1@6) (= _READ_SOURCE_$$localPos$1@6 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$localPos$1@6) (= _READ_SOURCE_$$localPos$1@6 #x00000000)) (and
(or %lbl%@26886 (=> (= (ControlFlow 0 8975) (- 0 26886)) (=> (not _WRITE_HAS_OCCURRED_$$localPos$1@4) (= _WRITE_SOURCE_$$localPos$1@4 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$localPos$1@4) (= _WRITE_SOURCE_$$localPos$1@4 #x00000000)) (and
(or %lbl%@26896 (=> (= (ControlFlow 0 8975) (- 0 26896)) (=> _READ_HAS_OCCURRED_$$newVelocity$1 false)))
(=> (=> _READ_HAS_OCCURRED_$$newVelocity$1 false) (and
(or %lbl%@26902 (=> (= (ControlFlow 0 8975) (- 0 26902)) (=> _WRITE_HAS_OCCURRED_$$newVelocity$1 (or
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000d)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000e)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000f)
(= _WRITE_SOURCE_$$newVelocity$1 #x00000010)))))
(=> (=> _WRITE_HAS_OCCURRED_$$newVelocity$1 (or
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000d)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000e)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000f)
(= _WRITE_SOURCE_$$newVelocity$1 #x00000010))) (and
(or %lbl%@26936 (=> (= (ControlFlow 0 8975) (- 0 26936)) (=> (not _READ_HAS_OCCURRED_$$newVelocity$1) (= _READ_SOURCE_$$newVelocity$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$newVelocity$1) (= _READ_SOURCE_$$newVelocity$1 #x00000000)) (and
(or %lbl%@26948 (=> (= (ControlFlow 0 8975) (- 0 26948)) (=> (not _WRITE_HAS_OCCURRED_$$newVelocity$1) (= _WRITE_SOURCE_$$newVelocity$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$newVelocity$1) (= _WRITE_SOURCE_$$newVelocity$1 #x00000000)) (and
(or %lbl%@26960 (=> (= (ControlFlow 0 8975) (- 0 26960)) (=> _READ_HAS_OCCURRED_$$newPosition$1 false)))
(=> (=> _READ_HAS_OCCURRED_$$newPosition$1 false) (and
(or %lbl%@26966 (=> (= (ControlFlow 0 8975) (- 0 26966)) (=> _WRITE_HAS_OCCURRED_$$newPosition$1 (or
(= _WRITE_SOURCE_$$newPosition$1 #x00000009)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000a)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000b)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000c)))))
(=> (=> _WRITE_HAS_OCCURRED_$$newPosition$1 (or
(= _WRITE_SOURCE_$$newPosition$1 #x00000009)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000a)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000b)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000c))) (and
(or %lbl%@27000 (=> (= (ControlFlow 0 8975) (- 0 27000)) (=> (not _READ_HAS_OCCURRED_$$newPosition$1) (= _READ_SOURCE_$$newPosition$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$newPosition$1) (= _READ_SOURCE_$$newPosition$1 #x00000000)) (and
(or %lbl%@27012 (=> (= (ControlFlow 0 8975) (- 0 27012)) (=> (not _WRITE_HAS_OCCURRED_$$newPosition$1) (= _WRITE_SOURCE_$$newPosition$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$newPosition$1) (= _WRITE_SOURCE_$$newPosition$1 #x00000000)) (and
(or %lbl%@27024 (=> (= (ControlFlow 0 8975) (- 0 27024)) (=> p2$1@4 p0$1@2)))
(=> (=> p2$1@4 p0$1@2) (and
(or %lbl%@27028 (=> (= (ControlFlow 0 8975) (- 0 27028)) (=> p2$2@4 p0$2@2)))
(=> (=> p2$2@4 p0$2@2) true))))))))))))))))))))))))))))))))))))))))))))))))))
(let (($for.cond5$5_correct (=> (and %lbl%+7448 true) (=> (= call3008formal@_offset$2@0 (bvadd (bvmul $j.0$2@2 #x00000004) #x00000003)) (and
(or %lbl%@26241 (=> (= (ControlFlow 0 7448) (- 0 26241)) (not (and
p3$2@2
_WRITE_HAS_OCCURRED_$$localPos$1@4
(= _WRITE_OFFSET_$$localPos$1@4 call3008formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)))))
(=> (not (and
p3$2@2
_WRITE_HAS_OCCURRED_$$localPos$1@4
(= _WRITE_OFFSET_$$localPos$1@4 call3008formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2))) (=> (and
(= v22$1@2 (ite p3$1@2 (FMUL32 v21$1@2 (FMUL32 (FMUL32 v20$1@2 v20$1@2) v20$1@2)) v22$1@1))
(= v22$2@2 (ite p3$2@2 (FMUL32 v21$2@2 (FMUL32 (FMUL32 v20$2@2 v20$2@2) v20$2@2)) v22$2@1))) (=> (and
(= $acc.1$1@3 (ite p3$1@2 (concat (concat (concat (FADD32 ((_ extract 127 96) $acc.1$1@2) (FMUL32 v22$1@2 (FSUB32 v16$1@2 v6$1@0))) (FADD32 ((_ extract 95 64) $acc.1$1@2) (FMUL32 v22$1@2 v19$1@2))) (FADD32 ((_ extract 63 32) $acc.1$1@2) (FMUL32 v22$1@2 v18$1@2))) (FADD32 ((_ extract 31 0) $acc.1$1@2) (FMUL32 v22$1@2 v17$1@2))) $acc.1$1@2))
(= $acc.1$2@3 (ite p3$2@2 (concat (concat (concat (FADD32 ((_ extract 127 96) $acc.1$2@2) (FMUL32 v22$2@2 (FSUB32 v16$2@2 v6$2@0))) (FADD32 ((_ extract 95 64) $acc.1$2@2) (FMUL32 v22$2@2 v19$2@2))) (FADD32 ((_ extract 63 32) $acc.1$2@2) (FMUL32 v22$2@2 v18$2@2))) (FADD32 ((_ extract 31 0) $acc.1$2@2) (FMUL32 v22$2@2 v17$2@2))) $acc.1$2@2))
(= $j.0$1@3 (ite p3$1@2 (bvadd $j.0$1@2 #x00000001) $j.0$1@2))
(= $j.0$2@3 (ite p3$2@2 (bvadd $j.0$2@2 #x00000001) $j.0$2@2))
(= p2$1@4 (ite p3$1@2 true p2$1@3))
(= p2$2@4 (ite p3$2@2 true p2$2@3))) (and
(=> (= (ControlFlow 0 7448) 8975) $for.cond5.backedge_correct)
(=> (= (ControlFlow 0 7448) 7983) $for.cond5.tail_correct))))))))))
(let ((inline$_LOG_READ_$$localPos$4$_LOG_READ_correct (=> (and %lbl%+7442 true) (=> (and
(= _READ_HAS_OCCURRED_$$localPos$1@6 (ite (and
p3$1@2
inline$_LOG_READ_$$localPos$4$track@2) true _READ_HAS_OCCURRED_$$localPos$1@5))
(= _READ_OFFSET_$$localPos$1@6 (ite (and
p3$1@2
inline$_LOG_READ_$$localPos$4$track@2) inline$_LOG_READ_$$localPos$4$_offset$1@2 _READ_OFFSET_$$localPos$1@5))
(= _READ_SOURCE_$$localPos$1@6 (ite (and
p3$1@2
inline$_LOG_READ_$$localPos$4$track@2) #x0000001d _READ_SOURCE_$$localPos$1@5))
(= (ControlFlow 0 7442) 7448)) $for.cond5$5_correct))))
(let ((inline$_LOG_READ_$$localPos$4$Entry_correct (=> (and %lbl%+7440 true) (=> (and
(= inline$_LOG_READ_$$localPos$4$_offset$1@2 (bvadd (bvmul $j.0$1@2 #x00000004) #x00000003))
(= (ControlFlow 0 7440) 7442)) inline$_LOG_READ_$$localPos$4$_LOG_READ_correct))))
(let (($for.cond5$4_correct (=> (and %lbl%+7446 true) (=> (= call2839formal@_offset$2@0 (bvadd (bvmul $j.0$2@2 #x00000004) #x00000003)) (and
(or %lbl%@25932 (=> (= (ControlFlow 0 7446) (- 0 25932)) (not (and
p3$2@2
_WRITE_HAS_OCCURRED_$$localPos$1@4
(= _WRITE_OFFSET_$$localPos$1@4 call2839formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)))))
(=> (not (and
p3$2@2
_WRITE_HAS_OCCURRED_$$localPos$1@4
(= _WRITE_OFFSET_$$localPos$1@4 call2839formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2))) (=> (and
(= v17$1@2 (ite p3$1@2 (FSUB32 v13$1@2 v3$1@0) v17$1@1))
(= v17$2@2 (ite p3$2@2 (FSUB32 v13$2@2 v3$2@0) v17$2@1))
(= v18$1@2 (ite p3$1@2 (FSUB32 v14$1@2 v4$1@0) v18$1@1))
(= v18$2@2 (ite p3$2@2 (FSUB32 v14$2@2 v4$2@0) v18$2@1))
(= v19$1@2 (ite p3$1@2 (FSUB32 v15$1@2 v5$1@0) v19$1@1))
(= v19$2@2 (ite p3$2@2 (FSUB32 v15$2@2 v5$2@0) v19$2@1))
(= v20$1@2 (ite p3$1@2 (FDIV32 #x3f800000 (FSQRT32 (FADD32 (FADD32 (FADD32 (FMUL32 v17$1@2 v17$1@2) (FMUL32 v18$1@2 v18$1@2)) (FMUL32 v19$1@2 v19$1@2)) $epsSqr$1))) v20$1@1))
(= v20$2@2 (ite p3$2@2 (FDIV32 #x3f800000 (FSQRT32 (FADD32 (FADD32 (FADD32 (FMUL32 v17$2@2 v17$2@2) (FMUL32 v18$2@2 v18$2@2)) (FMUL32 v19$2@2 v19$2@2)) $epsSqr$2))) v20$2@1))) (and
(or %lbl%@26120 (=> (= (ControlFlow 0 7446) (- 0 26120)) (=> p3$1@2 true)))
(=> (=> p3$1@2 true) (=> (and
(= v21$1@2 (ite p3$1@2 _HAVOC_bv32$1@14 v21$1@1))
(= v21$2@2 (ite p3$2@2 _HAVOC_bv32$2@14 v21$2@1))
(= (ControlFlow 0 7446) 7440)) inline$_LOG_READ_$$localPos$4$Entry_correct))))))))))
(let ((inline$_LOG_READ_$$localPos$3$_LOG_READ_correct (=> (and %lbl%+7360 true) (=> (and
(= _READ_HAS_OCCURRED_$$localPos$1@5 (ite (and
p3$1@2
inline$_LOG_READ_$$localPos$3$track@2) true _READ_HAS_OCCURRED_$$localPos$1@4))
(= _READ_OFFSET_$$localPos$1@5 (ite (and
p3$1@2
inline$_LOG_READ_$$localPos$3$track@2) inline$_LOG_READ_$$localPos$3$_offset$1@2 _READ_OFFSET_$$localPos$1@4))
(= _READ_SOURCE_$$localPos$1@5 (ite (and
p3$1@2
inline$_LOG_READ_$$localPos$3$track@2) #x0000001c _READ_SOURCE_$$localPos$1@4))
(= (ControlFlow 0 7360) 7446)) $for.cond5$4_correct))))
(let ((inline$_LOG_READ_$$localPos$3$Entry_correct (=> (and %lbl%+7358 true) (=> (and
(= inline$_LOG_READ_$$localPos$3$_offset$1@2 (bvadd (bvmul $j.0$1@2 #x00000004) #x00000003))
(= (ControlFlow 0 7358) 7360)) inline$_LOG_READ_$$localPos$3$_LOG_READ_correct))))
(let (($for.cond5$3_correct (=> (and %lbl%+7364 true) (=> (= call2786formal@_offset$2@0 (bvadd (bvmul $j.0$2@2 #x00000004) #x00000002)) (and
(or %lbl%@25775 (=> (= (ControlFlow 0 7364) (- 0 25775)) (not (and
p3$2@2
_WRITE_HAS_OCCURRED_$$localPos$1@4
(= _WRITE_OFFSET_$$localPos$1@4 call2786formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)))))
(=> (not (and
p3$2@2
_WRITE_HAS_OCCURRED_$$localPos$1@4
(= _WRITE_OFFSET_$$localPos$1@4 call2786formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2))) (and
(or %lbl%@25811 (=> (= (ControlFlow 0 7364) (- 0 25811)) (=> p3$1@2 true)))
(=> (=> p3$1@2 true) (=> (and
(= v16$1@2 (ite p3$1@2 _HAVOC_bv32$1@13 v16$1@1))
(= v16$2@2 (ite p3$2@2 _HAVOC_bv32$2@13 v16$2@1))
(= (ControlFlow 0 7364) 7358)) inline$_LOG_READ_$$localPos$3$Entry_correct)))))))))
(let ((inline$_LOG_READ_$$localPos$2$_LOG_READ_correct (=> (and %lbl%+7278 true) (=> (and
(= _READ_HAS_OCCURRED_$$localPos$1@4 (ite (and
p3$1@2
inline$_LOG_READ_$$localPos$2$track@2) true _READ_HAS_OCCURRED_$$localPos$1@3))
(= _READ_OFFSET_$$localPos$1@4 (ite (and
p3$1@2
inline$_LOG_READ_$$localPos$2$track@2) inline$_LOG_READ_$$localPos$2$_offset$1@2 _READ_OFFSET_$$localPos$1@3))
(= _READ_SOURCE_$$localPos$1@4 (ite (and
p3$1@2
inline$_LOG_READ_$$localPos$2$track@2) #x0000001b _READ_SOURCE_$$localPos$1@3))
(= (ControlFlow 0 7278) 7364)) $for.cond5$3_correct))))
(let ((inline$_LOG_READ_$$localPos$2$Entry_correct (=> (and %lbl%+7276 true) (=> (and
(= inline$_LOG_READ_$$localPos$2$_offset$1@2 (bvadd (bvmul $j.0$1@2 #x00000004) #x00000002))
(= (ControlFlow 0 7276) 7278)) inline$_LOG_READ_$$localPos$2$_LOG_READ_correct))))
(let (($for.cond5$2_correct (=> (and %lbl%+7282 true) (=> (= call2733formal@_offset$2@0 (bvadd (bvmul $j.0$2@2 #x00000004) #x00000001)) (and
(or %lbl%@25618 (=> (= (ControlFlow 0 7282) (- 0 25618)) (not (and
p3$2@2
_WRITE_HAS_OCCURRED_$$localPos$1@4
(= _WRITE_OFFSET_$$localPos$1@4 call2733formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)))))
(=> (not (and
p3$2@2
_WRITE_HAS_OCCURRED_$$localPos$1@4
(= _WRITE_OFFSET_$$localPos$1@4 call2733formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2))) (and
(or %lbl%@25654 (=> (= (ControlFlow 0 7282) (- 0 25654)) (=> p3$1@2 true)))
(=> (=> p3$1@2 true) (=> (and
(= v15$1@2 (ite p3$1@2 _HAVOC_bv32$1@12 v15$1@1))
(= v15$2@2 (ite p3$2@2 _HAVOC_bv32$2@12 v15$2@1))
(= (ControlFlow 0 7282) 7276)) inline$_LOG_READ_$$localPos$2$Entry_correct)))))))))
(let ((inline$_LOG_READ_$$localPos$1$_LOG_READ_correct (=> (and %lbl%+7196 true) (=> (and
(= _READ_HAS_OCCURRED_$$localPos$1@3 (ite (and
p3$1@2
inline$_LOG_READ_$$localPos$1$track@2) true _READ_HAS_OCCURRED_$$localPos$1@2))
(= _READ_OFFSET_$$localPos$1@3 (ite (and
p3$1@2
inline$_LOG_READ_$$localPos$1$track@2) inline$_LOG_READ_$$localPos$1$_offset$1@2 _READ_OFFSET_$$localPos$1@2))
(= _READ_SOURCE_$$localPos$1@3 (ite (and
p3$1@2
inline$_LOG_READ_$$localPos$1$track@2) #x0000001a _READ_SOURCE_$$localPos$1@2))
(= (ControlFlow 0 7196) 7282)) $for.cond5$2_correct))))
(let ((inline$_LOG_READ_$$localPos$1$Entry_correct (=> (and %lbl%+7194 true) (=> (and
(= inline$_LOG_READ_$$localPos$1$_offset$1@2 (bvadd (bvmul $j.0$1@2 #x00000004) #x00000001))
(= (ControlFlow 0 7194) 7196)) inline$_LOG_READ_$$localPos$1$_LOG_READ_correct))))
(let (($for.cond5$1_correct (=> (and %lbl%+7200 true) (=> (= call2680formal@_offset$2@0 (bvmul $j.0$2@2 #x00000004)) (and
(or %lbl%@25461 (=> (= (ControlFlow 0 7200) (- 0 25461)) (not (and
p3$2@2
_WRITE_HAS_OCCURRED_$$localPos$1@4
(= _WRITE_OFFSET_$$localPos$1@4 call2680formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)))))
(=> (not (and
p3$2@2
_WRITE_HAS_OCCURRED_$$localPos$1@4
(= _WRITE_OFFSET_$$localPos$1@4 call2680formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2))) (and
(or %lbl%@25497 (=> (= (ControlFlow 0 7200) (- 0 25497)) (=> p3$1@2 true)))
(=> (=> p3$1@2 true) (=> (and
(= v14$1@2 (ite p3$1@2 _HAVOC_bv32$1@11 v14$1@1))
(= v14$2@2 (ite p3$2@2 _HAVOC_bv32$2@11 v14$2@1))
(= (ControlFlow 0 7200) 7194)) inline$_LOG_READ_$$localPos$1$Entry_correct)))))))))
(let ((inline$_LOG_READ_$$localPos$0$_LOG_READ_correct (=> (and %lbl%+7114 true) (=> (and
(= _READ_HAS_OCCURRED_$$localPos$1@2 (ite (and
p3$1@2
inline$_LOG_READ_$$localPos$0$track@2) true _READ_HAS_OCCURRED_$$localPos$1@1))
(= _READ_OFFSET_$$localPos$1@2 (ite (and
p3$1@2
inline$_LOG_READ_$$localPos$0$track@2) inline$_LOG_READ_$$localPos$0$_offset$1@2 _READ_OFFSET_$$localPos$1@1))
(= _READ_SOURCE_$$localPos$1@2 (ite (and
p3$1@2
inline$_LOG_READ_$$localPos$0$track@2) #x00000019 _READ_SOURCE_$$localPos$1@1))
(= (ControlFlow 0 7114) 7200)) $for.cond5$1_correct))))
(let ((inline$_LOG_READ_$$localPos$0$Entry_correct (=> (and %lbl%+7112 true) (=> (and
(= inline$_LOG_READ_$$localPos$0$_offset$1@2 (bvmul $j.0$1@2 #x00000004))
(= (ControlFlow 0 7112) 7114)) inline$_LOG_READ_$$localPos$0$_LOG_READ_correct))))
(let (($for.cond5_correct (=> (and %lbl%+7118 true) (=> (=> _b11 (=> _READ_HAS_OCCURRED_$$localPos$1@1 (or
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@1) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvmul #x00000000 #x00000004)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@1) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000001)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@1) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000002)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@1) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@1) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003)))))) (=> (and
(=> _READ_HAS_OCCURRED_$$vel$1 (or
(= _READ_SOURCE_$$vel$1 #x00000005)
(= _READ_SOURCE_$$vel$1 #x00000006)
(= _READ_SOURCE_$$vel$1 #x00000007)
(= _READ_SOURCE_$$vel$1 #x00000008)))
(=> _WRITE_HAS_OCCURRED_$$vel$1 false)
(=> (not _READ_HAS_OCCURRED_$$vel$1) (= _READ_SOURCE_$$vel$1 #x00000000))
(=> (not _WRITE_HAS_OCCURRED_$$vel$1) (= _WRITE_SOURCE_$$vel$1 #x00000000))) (=> (and
(=> _READ_HAS_OCCURRED_$$pos$1@8 (or
(= _READ_SOURCE_$$pos$1@8 #x00000001)
(= _READ_SOURCE_$$pos$1@8 #x00000002)
(= _READ_SOURCE_$$pos$1@8 #x00000003)
(= _READ_SOURCE_$$pos$1@8 #x00000004)
(= _READ_SOURCE_$$pos$1@8 #x00000011)
(= _READ_SOURCE_$$pos$1@8 #x00000012)
(= _READ_SOURCE_$$pos$1@8 #x00000013)
(= _READ_SOURCE_$$pos$1@8 #x00000014)))
(=> _WRITE_HAS_OCCURRED_$$pos$1 false)
(=> (not _READ_HAS_OCCURRED_$$pos$1@8) (= _READ_SOURCE_$$pos$1@8 #x00000000))
(=> (not _WRITE_HAS_OCCURRED_$$pos$1) (= _WRITE_SOURCE_$$pos$1 #x00000000))
(=> _READ_HAS_OCCURRED_$$localPos$1@1 (or
(= _READ_SOURCE_$$localPos$1@1 #x00000019)
(= _READ_SOURCE_$$localPos$1@1 #x0000001a)
(= _READ_SOURCE_$$localPos$1@1 #x0000001b)
(= _READ_SOURCE_$$localPos$1@1 #x0000001c)
(= _READ_SOURCE_$$localPos$1@1 #x0000001d)))
(=> _WRITE_HAS_OCCURRED_$$localPos$1@4 (or
(= _WRITE_SOURCE_$$localPos$1@4 #x00000015)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000016)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000017)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000018)))
(=> (not _READ_HAS_OCCURRED_$$localPos$1@1) (= _READ_SOURCE_$$localPos$1@1 #x00000000))
(=> (not _WRITE_HAS_OCCURRED_$$localPos$1@4) (= _WRITE_SOURCE_$$localPos$1@4 #x00000000))) (=> (and
(=> _READ_HAS_OCCURRED_$$newVelocity$1 false)
(=> _WRITE_HAS_OCCURRED_$$newVelocity$1 (or
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000d)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000e)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000f)
(= _WRITE_SOURCE_$$newVelocity$1 #x00000010)))
(=> (not _READ_HAS_OCCURRED_$$newVelocity$1) (= _READ_SOURCE_$$newVelocity$1 #x00000000))
(=> (not _WRITE_HAS_OCCURRED_$$newVelocity$1) (= _WRITE_SOURCE_$$newVelocity$1 #x00000000))
(=> _READ_HAS_OCCURRED_$$newPosition$1 false)
(=> _WRITE_HAS_OCCURRED_$$newPosition$1 (or
(= _WRITE_SOURCE_$$newPosition$1 #x00000009)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000a)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000b)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000c)))
(=> (not _READ_HAS_OCCURRED_$$newPosition$1) (= _READ_SOURCE_$$newPosition$1 #x00000000))
(=> (not _WRITE_HAS_OCCURRED_$$newPosition$1) (= _WRITE_SOURCE_$$newPosition$1 #x00000000))
(=> p2$1@2 p0$1@2)
(=> p2$2@2 p0$2@2)
(= v12$1@2 (ite p2$1@2 (bvult $j.0$1@2 v2$1@0) v12$1@1))
(= v12$2@2 (ite p2$2@2 (bvult $j.0$2@2 v2$2@0) v12$2@1))
(= p3$1@2 (ite p2$1@2 v12$1@2 false))
(= p3$2@2 (ite p2$2@2 v12$2@2 false))
(= p2$1@3 (ite p2$1@2 v12$1@2 p2$1@2))
(= p2$2@3 (ite p2$2@2 v12$2@2 p2$2@2))) (and
(or %lbl%@25348 (=> (= (ControlFlow 0 7118) (- 0 25348)) (=> p3$1@2 true)))
(=> (=> p3$1@2 true) (=> (and
(= v13$1@2 (ite p3$1@2 _HAVOC_bv32$1@10 v13$1@1))
(= v13$2@2 (ite p3$2@2 _HAVOC_bv32$2@10 v13$2@1))
(= (ControlFlow 0 7118) 7112)) inline$_LOG_READ_$$localPos$0$Entry_correct))))))))))
(let (($for.cond$9_correct (=> (and %lbl%+7036 true) (=> (and
(= $acc.1$1@1 (ite p1$1@1 $acc.0$1@1 $acc.1$1@0))
(= $acc.1$2@1 (ite p1$2@1 $acc.0$2@1 $acc.1$2@0))
(= $j.0$1@1 (ite p1$1@1 #x00000000 $j.0$1@0))
(= $j.0$2@1 (ite p1$2@1 #x00000000 $j.0$2@0))
(= p2$1@1 (ite p1$1@1 true false))
(= p2$2@1 (ite p1$2@1 true false))) (and
(or %lbl%@23930 (=> (= (ControlFlow 0 7036) (- 0 23930)) (=> _b11 (=> _READ_HAS_OCCURRED_$$localPos$1@0 (or
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@0) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvmul #x00000000 #x00000004)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@0) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000001)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@0) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000002)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@0) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@0) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003))))))))
(=> (=> _b11 (=> _READ_HAS_OCCURRED_$$localPos$1@0 (or
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@0) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvmul #x00000000 #x00000004)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@0) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000001)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@0) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000002)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@0) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@0) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003)))))) (and
(or %lbl%@24126 (=> (= (ControlFlow 0 7036) (- 0 24126)) (=> _READ_HAS_OCCURRED_$$vel$1 (or
(= _READ_SOURCE_$$vel$1 #x00000005)
(= _READ_SOURCE_$$vel$1 #x00000006)
(= _READ_SOURCE_$$vel$1 #x00000007)
(= _READ_SOURCE_$$vel$1 #x00000008)))))
(=> (=> _READ_HAS_OCCURRED_$$vel$1 (or
(= _READ_SOURCE_$$vel$1 #x00000005)
(= _READ_SOURCE_$$vel$1 #x00000006)
(= _READ_SOURCE_$$vel$1 #x00000007)
(= _READ_SOURCE_$$vel$1 #x00000008))) (and
(or %lbl%@24160 (=> (= (ControlFlow 0 7036) (- 0 24160)) (=> _WRITE_HAS_OCCURRED_$$vel$1 false)))
(=> (=> _WRITE_HAS_OCCURRED_$$vel$1 false) (and
(or %lbl%@24166 (=> (= (ControlFlow 0 7036) (- 0 24166)) (=> (not _READ_HAS_OCCURRED_$$vel$1) (= _READ_SOURCE_$$vel$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$vel$1) (= _READ_SOURCE_$$vel$1 #x00000000)) (and
(or %lbl%@24178 (=> (= (ControlFlow 0 7036) (- 0 24178)) (=> (not _WRITE_HAS_OCCURRED_$$vel$1) (= _WRITE_SOURCE_$$vel$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$vel$1) (= _WRITE_SOURCE_$$vel$1 #x00000000)) (and
(or %lbl%@24190 (=> (= (ControlFlow 0 7036) (- 0 24190)) (=> _READ_HAS_OCCURRED_$$pos$1@8 (or
(= _READ_SOURCE_$$pos$1@8 #x00000001)
(= _READ_SOURCE_$$pos$1@8 #x00000002)
(= _READ_SOURCE_$$pos$1@8 #x00000003)
(= _READ_SOURCE_$$pos$1@8 #x00000004)
(= _READ_SOURCE_$$pos$1@8 #x00000011)
(= _READ_SOURCE_$$pos$1@8 #x00000012)
(= _READ_SOURCE_$$pos$1@8 #x00000013)
(= _READ_SOURCE_$$pos$1@8 #x00000014)))))
(=> (=> _READ_HAS_OCCURRED_$$pos$1@8 (or
(= _READ_SOURCE_$$pos$1@8 #x00000001)
(= _READ_SOURCE_$$pos$1@8 #x00000002)
(= _READ_SOURCE_$$pos$1@8 #x00000003)
(= _READ_SOURCE_$$pos$1@8 #x00000004)
(= _READ_SOURCE_$$pos$1@8 #x00000011)
(= _READ_SOURCE_$$pos$1@8 #x00000012)
(= _READ_SOURCE_$$pos$1@8 #x00000013)
(= _READ_SOURCE_$$pos$1@8 #x00000014))) (and
(or %lbl%@24247 (=> (= (ControlFlow 0 7036) (- 0 24247)) (=> _WRITE_HAS_OCCURRED_$$pos$1 false)))
(=> (=> _WRITE_HAS_OCCURRED_$$pos$1 false) (and
(or %lbl%@24253 (=> (= (ControlFlow 0 7036) (- 0 24253)) (=> (not _READ_HAS_OCCURRED_$$pos$1@8) (= _READ_SOURCE_$$pos$1@8 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$pos$1@8) (= _READ_SOURCE_$$pos$1@8 #x00000000)) (and
(or %lbl%@24263 (=> (= (ControlFlow 0 7036) (- 0 24263)) (=> (not _WRITE_HAS_OCCURRED_$$pos$1) (= _WRITE_SOURCE_$$pos$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$pos$1) (= _WRITE_SOURCE_$$pos$1 #x00000000)) (and
(or %lbl%@24275 (=> (= (ControlFlow 0 7036) (- 0 24275)) (=> _READ_HAS_OCCURRED_$$localPos$1@0 (or
(= _READ_SOURCE_$$localPos$1@0 #x00000019)
(= _READ_SOURCE_$$localPos$1@0 #x0000001a)
(= _READ_SOURCE_$$localPos$1@0 #x0000001b)
(= _READ_SOURCE_$$localPos$1@0 #x0000001c)
(= _READ_SOURCE_$$localPos$1@0 #x0000001d)))))
(=> (=> _READ_HAS_OCCURRED_$$localPos$1@0 (or
(= _READ_SOURCE_$$localPos$1@0 #x00000019)
(= _READ_SOURCE_$$localPos$1@0 #x0000001a)
(= _READ_SOURCE_$$localPos$1@0 #x0000001b)
(= _READ_SOURCE_$$localPos$1@0 #x0000001c)
(= _READ_SOURCE_$$localPos$1@0 #x0000001d))) (and
(or %lbl%@24311 (=> (= (ControlFlow 0 7036) (- 0 24311)) (=> _WRITE_HAS_OCCURRED_$$localPos$1@4 (or
(= _WRITE_SOURCE_$$localPos$1@4 #x00000015)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000016)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000017)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000018)))))
(=> (=> _WRITE_HAS_OCCURRED_$$localPos$1@4 (or
(= _WRITE_SOURCE_$$localPos$1@4 #x00000015)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000016)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000017)
(= _WRITE_SOURCE_$$localPos$1@4 #x00000018))) (and
(or %lbl%@24340 (=> (= (ControlFlow 0 7036) (- 0 24340)) (=> (not _READ_HAS_OCCURRED_$$localPos$1@0) (= _READ_SOURCE_$$localPos$1@0 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$localPos$1@0) (= _READ_SOURCE_$$localPos$1@0 #x00000000)) (and
(or %lbl%@24350 (=> (= (ControlFlow 0 7036) (- 0 24350)) (=> (not _WRITE_HAS_OCCURRED_$$localPos$1@4) (= _WRITE_SOURCE_$$localPos$1@4 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$localPos$1@4) (= _WRITE_SOURCE_$$localPos$1@4 #x00000000)) (and
(or %lbl%@24360 (=> (= (ControlFlow 0 7036) (- 0 24360)) (=> _READ_HAS_OCCURRED_$$newVelocity$1 false)))
(=> (=> _READ_HAS_OCCURRED_$$newVelocity$1 false) (and
(or %lbl%@24366 (=> (= (ControlFlow 0 7036) (- 0 24366)) (=> _WRITE_HAS_OCCURRED_$$newVelocity$1 (or
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000d)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000e)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000f)
(= _WRITE_SOURCE_$$newVelocity$1 #x00000010)))))
(=> (=> _WRITE_HAS_OCCURRED_$$newVelocity$1 (or
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000d)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000e)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000f)
(= _WRITE_SOURCE_$$newVelocity$1 #x00000010))) (and
(or %lbl%@24400 (=> (= (ControlFlow 0 7036) (- 0 24400)) (=> (not _READ_HAS_OCCURRED_$$newVelocity$1) (= _READ_SOURCE_$$newVelocity$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$newVelocity$1) (= _READ_SOURCE_$$newVelocity$1 #x00000000)) (and
(or %lbl%@24412 (=> (= (ControlFlow 0 7036) (- 0 24412)) (=> (not _WRITE_HAS_OCCURRED_$$newVelocity$1) (= _WRITE_SOURCE_$$newVelocity$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$newVelocity$1) (= _WRITE_SOURCE_$$newVelocity$1 #x00000000)) (and
(or %lbl%@24424 (=> (= (ControlFlow 0 7036) (- 0 24424)) (=> _READ_HAS_OCCURRED_$$newPosition$1 false)))
(=> (=> _READ_HAS_OCCURRED_$$newPosition$1 false) (and
(or %lbl%@24430 (=> (= (ControlFlow 0 7036) (- 0 24430)) (=> _WRITE_HAS_OCCURRED_$$newPosition$1 (or
(= _WRITE_SOURCE_$$newPosition$1 #x00000009)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000a)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000b)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000c)))))
(=> (=> _WRITE_HAS_OCCURRED_$$newPosition$1 (or
(= _WRITE_SOURCE_$$newPosition$1 #x00000009)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000a)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000b)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000c))) (and
(or %lbl%@24464 (=> (= (ControlFlow 0 7036) (- 0 24464)) (=> (not _READ_HAS_OCCURRED_$$newPosition$1) (= _READ_SOURCE_$$newPosition$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$newPosition$1) (= _READ_SOURCE_$$newPosition$1 #x00000000)) (and
(or %lbl%@24476 (=> (= (ControlFlow 0 7036) (- 0 24476)) (=> (not _WRITE_HAS_OCCURRED_$$newPosition$1) (= _WRITE_SOURCE_$$newPosition$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$newPosition$1) (= _WRITE_SOURCE_$$newPosition$1 #x00000000)) (and
(or %lbl%@24488 (=> (= (ControlFlow 0 7036) (- 0 24488)) (=> p2$1@1 p0$1@2)))
(=> (=> p2$1@1 p0$1@2) (and
(or %lbl%@24492 (=> (= (ControlFlow 0 7036) (- 0 24492)) (=> p2$2@1 p0$2@2)))
(=> (=> p2$2@1 p0$2@2) (=> (= (ControlFlow 0 7036) 7118) $for.cond5_correct)))))))))))))))))))))))))))))))))))))))))))))))))))
(let ((inline$$bugle_barrier$0$Return_correct (=> (and %lbl%+7032 true) (=> (= (ControlFlow 0 7032) 7036) $for.cond$9_correct))))
(let ((inline$$bugle_barrier$0$anon18_Else_correct (=> (and %lbl%+7020 true) (=> (and
(not (and
p1$2@1
(= inline$$bugle_barrier$0$$1$2@1 #b1)))
(= (ControlFlow 0 7020) 7032)) inline$$bugle_barrier$0$Return_correct))))
(let ((inline$$bugle_barrier$0$anon18_Then_correct (=> (and %lbl%+7022 true) (=> (and
p1$2@1
(= inline$$bugle_barrier$0$$1$2@1 #b1)
(= (ControlFlow 0 7022) 7032)) inline$$bugle_barrier$0$Return_correct))))
(let ((inline$$bugle_barrier$0$anon9_correct (=> (and %lbl%+7018 true) (and
(=> (= (ControlFlow 0 7018) 7022) inline$$bugle_barrier$0$anon18_Then_correct)
(=> (= (ControlFlow 0 7018) 7020) inline$$bugle_barrier$0$anon18_Else_correct)))))
(let ((inline$$bugle_barrier$0$anon17_Else_correct (=> (and %lbl%+7016 true) (=> (and
(not (and
p1$1@1
(= inline$$bugle_barrier$0$$1$1@1 #b1)))
(= (ControlFlow 0 7016) 7018)) inline$$bugle_barrier$0$anon9_correct))))
(let ((inline$$bugle_barrier$0$anon17_Then_correct (=> (and %lbl%+7024 true) (=> (and
p1$1@1
(= inline$$bugle_barrier$0$$1$1@1 #b1)) (=> (and
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _READ_HAS_OCCURRED_$$pos$1@8))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _WRITE_HAS_OCCURRED_$$pos$1))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _READ_HAS_OCCURRED_$$vel$1))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _WRITE_HAS_OCCURRED_$$vel$1))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _READ_HAS_OCCURRED_$$newPosition$1))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _WRITE_HAS_OCCURRED_$$newPosition$1))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _READ_HAS_OCCURRED_$$newVelocity$1))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _WRITE_HAS_OCCURRED_$$newVelocity$1))) (and
(=> (= (ControlFlow 0 7024) 7022) inline$$bugle_barrier$0$anon18_Then_correct)
(=> (= (ControlFlow 0 7024) 7020) inline$$bugle_barrier$0$anon18_Else_correct)))))))
(let ((inline$$bugle_barrier$0$anon4_correct (=> (and %lbl%+7014 true) (and
(=> (= (ControlFlow 0 7014) 7024) inline$$bugle_barrier$0$anon17_Then_correct)
(=> (= (ControlFlow 0 7014) 7016) inline$$bugle_barrier$0$anon17_Else_correct)))))
(let ((inline$$bugle_barrier$0$anon16_Else_correct (=> (and %lbl%+7012 true) (=> (and
(not (and
p1$2@1
(= inline$$bugle_barrier$0$$0$2@1 #b1)))
(= (ControlFlow 0 7012) 7014)) inline$$bugle_barrier$0$anon4_correct))))
(let ((inline$$bugle_barrier$0$anon16_Then_correct (=> (and %lbl%+7026 true) (=> (and
p1$2@1
(= inline$$bugle_barrier$0$$0$2@1 #b1)) (and
(=> (= (ControlFlow 0 7026) 7024) inline$$bugle_barrier$0$anon17_Then_correct)
(=> (= (ControlFlow 0 7026) 7016) inline$$bugle_barrier$0$anon17_Else_correct))))))
(let ((inline$$bugle_barrier$0$anon2_correct (=> (and %lbl%+7010 true) (and
(=> (= (ControlFlow 0 7010) 7026) inline$$bugle_barrier$0$anon16_Then_correct)
(=> (= (ControlFlow 0 7010) 7012) inline$$bugle_barrier$0$anon16_Else_correct)))))
(let ((inline$$bugle_barrier$0$anon15_Else_correct (=> (and %lbl%+7008 true) (=> (and
(not (and
p1$1@1
(= inline$$bugle_barrier$0$$0$1@1 #b1)))
(= (ControlFlow 0 7008) 7010)) inline$$bugle_barrier$0$anon2_correct))))
(let ((inline$$bugle_barrier$0$anon15_Then_correct (=> (and %lbl%+7028 true) (=> (and
p1$1@1
(= inline$$bugle_barrier$0$$0$1@1 #b1)
(not _READ_HAS_OCCURRED_$$localPos$1@0)
(not _WRITE_HAS_OCCURRED_$$localPos$1@4)) (and
(=> (= (ControlFlow 0 7028) 7026) inline$$bugle_barrier$0$anon16_Then_correct)
(=> (= (ControlFlow 0 7028) 7012) inline$$bugle_barrier$0$anon16_Else_correct))))))
(let ((inline$$bugle_barrier$0$anon14_Else_correct (=> (and %lbl%+7006 true) (=> (not (or
(and
(not p1$1@1)
(not p1$2@1))
(and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)
(or
(not p1$1@1)
(not p1$2@1))))) (and
(=> (= (ControlFlow 0 7006) 7028) inline$$bugle_barrier$0$anon15_Then_correct)
(=> (= (ControlFlow 0 7006) 7008) inline$$bugle_barrier$0$anon15_Else_correct))))))
(let ((inline$$bugle_barrier$0$anon14_Then_correct (=> (and %lbl%+7030 true) (=> (and
(or
(and
(not p1$1@1)
(not p1$2@1))
(and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)
(or
(not p1$1@1)
(not p1$2@1))))
(= (ControlFlow 0 7030) 7036)) $for.cond$9_correct))))
(let ((inline$$bugle_barrier$0$Entry_correct (=> (and %lbl%+7002 true) (=> (and
(= inline$$bugle_barrier$0$$0$1@1 (ite true #b1 #b0))
(= inline$$bugle_barrier$0$$1$1@1 (ite false #b1 #b0))
(= inline$$bugle_barrier$0$$0$2@1 (ite true #b1 #b0))
(= inline$$bugle_barrier$0$$1$2@1 (ite false #b1 #b0))) (and
(or %lbl%@23449 (=> (= (ControlFlow 0 7002) (- 0 23449)) (=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (= p1$1@1 p1$2@1))))
(=> (=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (= p1$1@1 p1$2@1)) (and
(=> (= (ControlFlow 0 7002) 7030) inline$$bugle_barrier$0$anon14_Then_correct)
(=> (= (ControlFlow 0 7002) 7006) inline$$bugle_barrier$0$anon14_Else_correct))))))))
(let (($for.cond$8_correct (=> (and %lbl%+7034 true) (=> (= call2152formal@_offset$2@0 (bvadd (bvmul v0$2@0 #x00000004) #x00000003)) (and
(or %lbl%@23317 (=> (= (ControlFlow 0 7034) (- 0 23317)) (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$localPos$1@4
(= _WRITE_OFFSET_$$localPos$1@4 call2152formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)))))
(=> (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$localPos$1@4
(= _WRITE_OFFSET_$$localPos$1@4 call2152formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2))) (and
(or %lbl%@23353 (=> (= (ControlFlow 0 7034) (- 0 23353)) (not (and
p1$2@1
_READ_HAS_OCCURRED_$$localPos$1@0
(= _READ_OFFSET_$$localPos$1@0 call2152formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)))))
(=> (not (and
p1$2@1
_READ_HAS_OCCURRED_$$localPos$1@0
(= _READ_OFFSET_$$localPos$1@0 call2152formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2))) (=> (= (ControlFlow 0 7034) 7002) inline$$bugle_barrier$0$Entry_correct)))))))))
(let ((inline$_LOG_WRITE_$$localPos$3$_LOG_WRITE_correct (=> (and %lbl%+6495 true) (=> (and
(= _WRITE_HAS_OCCURRED_$$localPos$1@4 (ite (and
p1$1@1
inline$_LOG_WRITE_$$localPos$3$track@1) true _WRITE_HAS_OCCURRED_$$localPos$1@3))
(= _WRITE_OFFSET_$$localPos$1@4 (ite (and
p1$1@1
inline$_LOG_WRITE_$$localPos$3$track@1) inline$_LOG_WRITE_$$localPos$3$_offset$1@1 _WRITE_OFFSET_$$localPos$1@3))
(= _WRITE_SOURCE_$$localPos$1@4 (ite (and
p1$1@1
inline$_LOG_WRITE_$$localPos$3$track@1) #x00000018 _WRITE_SOURCE_$$localPos$1@3))
(= (ControlFlow 0 6495) 7034)) $for.cond$8_correct))))
(let ((inline$_LOG_WRITE_$$localPos$3$Entry_correct (=> (and %lbl%+6493 true) (=> (and
(= inline$_LOG_WRITE_$$localPos$3$_offset$1@1 (bvadd (bvmul v0$1@0 #x00000004) #x00000003))
(= (ControlFlow 0 6493) 6495)) inline$_LOG_WRITE_$$localPos$3$_LOG_WRITE_correct))))
(let (($for.cond$7_correct (=> (and %lbl%+6499 true) (=> (= call2115formal@_offset$2@0 (bvadd (bvmul v0$2@0 #x00000004) #x00000002)) (and
(or %lbl%@23151 (=> (= (ControlFlow 0 6499) (- 0 23151)) (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$localPos$1@3
(= _WRITE_OFFSET_$$localPos$1@3 call2115formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)))))
(=> (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$localPos$1@3
(= _WRITE_OFFSET_$$localPos$1@3 call2115formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2))) (and
(or %lbl%@23187 (=> (= (ControlFlow 0 6499) (- 0 23187)) (not (and
p1$2@1
_READ_HAS_OCCURRED_$$localPos$1@0
(= _READ_OFFSET_$$localPos$1@0 call2115formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)))))
(=> (not (and
p1$2@1
_READ_HAS_OCCURRED_$$localPos$1@0
(= _READ_OFFSET_$$localPos$1@0 call2115formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2))) (and
(or %lbl%@23223 (=> (= (ControlFlow 0 6499) (- 0 23223)) (=> p1$1@1 true)))
(=> (=> p1$1@1 true) (=> (= (ControlFlow 0 6499) 6493) inline$_LOG_WRITE_$$localPos$3$Entry_correct)))))))))))
(let ((inline$_LOG_WRITE_$$localPos$2$_LOG_WRITE_correct (=> (and %lbl%+6413 true) (=> (and
(= _WRITE_HAS_OCCURRED_$$localPos$1@3 (ite (and
p1$1@1
inline$_LOG_WRITE_$$localPos$2$track@1) true _WRITE_HAS_OCCURRED_$$localPos$1@2))
(= _WRITE_OFFSET_$$localPos$1@3 (ite (and
p1$1@1
inline$_LOG_WRITE_$$localPos$2$track@1) inline$_LOG_WRITE_$$localPos$2$_offset$1@1 _WRITE_OFFSET_$$localPos$1@2))
(= _WRITE_SOURCE_$$localPos$1@3 (ite (and
p1$1@1
inline$_LOG_WRITE_$$localPos$2$track@1) #x00000017 _WRITE_SOURCE_$$localPos$1@2))
(= (ControlFlow 0 6413) 6499)) $for.cond$7_correct))))
(let ((inline$_LOG_WRITE_$$localPos$2$Entry_correct (=> (and %lbl%+6411 true) (=> (and
(= inline$_LOG_WRITE_$$localPos$2$_offset$1@1 (bvadd (bvmul v0$1@0 #x00000004) #x00000002))
(= (ControlFlow 0 6411) 6413)) inline$_LOG_WRITE_$$localPos$2$_LOG_WRITE_correct))))
(let (($for.cond$6_correct (=> (and %lbl%+6417 true) (=> (= call2078formal@_offset$2@0 (bvadd (bvmul v0$2@0 #x00000004) #x00000001)) (and
(or %lbl%@22985 (=> (= (ControlFlow 0 6417) (- 0 22985)) (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$localPos$1@2
(= _WRITE_OFFSET_$$localPos$1@2 call2078formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)))))
(=> (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$localPos$1@2
(= _WRITE_OFFSET_$$localPos$1@2 call2078formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2))) (and
(or %lbl%@23021 (=> (= (ControlFlow 0 6417) (- 0 23021)) (not (and
p1$2@1
_READ_HAS_OCCURRED_$$localPos$1@0
(= _READ_OFFSET_$$localPos$1@0 call2078formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)))))
(=> (not (and
p1$2@1
_READ_HAS_OCCURRED_$$localPos$1@0
(= _READ_OFFSET_$$localPos$1@0 call2078formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2))) (and
(or %lbl%@23057 (=> (= (ControlFlow 0 6417) (- 0 23057)) (=> p1$1@1 true)))
(=> (=> p1$1@1 true) (=> (= (ControlFlow 0 6417) 6411) inline$_LOG_WRITE_$$localPos$2$Entry_correct)))))))))))
(let ((inline$_LOG_WRITE_$$localPos$1$_LOG_WRITE_correct (=> (and %lbl%+6331 true) (=> (and
(= _WRITE_HAS_OCCURRED_$$localPos$1@2 (ite (and
p1$1@1
inline$_LOG_WRITE_$$localPos$1$track@1) true _WRITE_HAS_OCCURRED_$$localPos$1@1))
(= _WRITE_OFFSET_$$localPos$1@2 (ite (and
p1$1@1
inline$_LOG_WRITE_$$localPos$1$track@1) inline$_LOG_WRITE_$$localPos$1$_offset$1@1 _WRITE_OFFSET_$$localPos$1@1))
(= _WRITE_SOURCE_$$localPos$1@2 (ite (and
p1$1@1
inline$_LOG_WRITE_$$localPos$1$track@1) #x00000016 _WRITE_SOURCE_$$localPos$1@1))
(= (ControlFlow 0 6331) 6417)) $for.cond$6_correct))))
(let ((inline$_LOG_WRITE_$$localPos$1$Entry_correct (=> (and %lbl%+6329 true) (=> (and
(= inline$_LOG_WRITE_$$localPos$1$_offset$1@1 (bvadd (bvmul v0$1@0 #x00000004) #x00000001))
(= (ControlFlow 0 6329) 6331)) inline$_LOG_WRITE_$$localPos$1$_LOG_WRITE_correct))))
(let (($for.cond$5_correct (=> (and %lbl%+6335 true) (=> (= call2041formal@_offset$2@0 (bvmul v0$2@0 #x00000004)) (and
(or %lbl%@22819 (=> (= (ControlFlow 0 6335) (- 0 22819)) (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$localPos$1@1
(= _WRITE_OFFSET_$$localPos$1@1 call2041formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)))))
(=> (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$localPos$1@1
(= _WRITE_OFFSET_$$localPos$1@1 call2041formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2))) (and
(or %lbl%@22855 (=> (= (ControlFlow 0 6335) (- 0 22855)) (not (and
p1$2@1
_READ_HAS_OCCURRED_$$localPos$1@0
(= _READ_OFFSET_$$localPos$1@0 call2041formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)))))
(=> (not (and
p1$2@1
_READ_HAS_OCCURRED_$$localPos$1@0
(= _READ_OFFSET_$$localPos$1@0 call2041formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2))) (and
(or %lbl%@22891 (=> (= (ControlFlow 0 6335) (- 0 22891)) (=> p1$1@1 true)))
(=> (=> p1$1@1 true) (=> (= (ControlFlow 0 6335) 6329) inline$_LOG_WRITE_$$localPos$1$Entry_correct)))))))))))
(let ((inline$_LOG_WRITE_$$localPos$0$_LOG_WRITE_correct (=> (and %lbl%+6249 true) (=> (and
(= _WRITE_HAS_OCCURRED_$$localPos$1@1 (ite (and
p1$1@1
inline$_LOG_WRITE_$$localPos$0$track@1) true _WRITE_HAS_OCCURRED_$$localPos$1@0))
(= _WRITE_OFFSET_$$localPos$1@1 (ite (and
p1$1@1
inline$_LOG_WRITE_$$localPos$0$track@1) inline$_LOG_WRITE_$$localPos$0$_offset$1@1 _WRITE_OFFSET_$$localPos$1@0))
(= _WRITE_SOURCE_$$localPos$1@1 (ite (and
p1$1@1
inline$_LOG_WRITE_$$localPos$0$track@1) #x00000015 _WRITE_SOURCE_$$localPos$1@0))
(= (ControlFlow 0 6249) 6335)) $for.cond$5_correct))))
(let ((inline$_LOG_WRITE_$$localPos$0$Entry_correct (=> (and %lbl%+6247 true) (=> (and
(= inline$_LOG_WRITE_$$localPos$0$_offset$1@1 (bvmul v0$1@0 #x00000004))
(= (ControlFlow 0 6247) 6249)) inline$_LOG_WRITE_$$localPos$0$_LOG_WRITE_correct))))
(let (($for.cond$4_correct (=> (and %lbl%+6253 true) (=> (= call2010formal@_offset$2@0 (bvadd (bvmul (bvadd (bvmul $i.0$2@1 v2$2@0) v0$2@0) #x00000004) #x00000003)) (and
(or %lbl%@22719 (=> (= (ControlFlow 0 6253) (- 0 22719)) (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$pos$1
(= _WRITE_OFFSET_$$pos$1 call2010formal@_offset$2@0)))))
(=> (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$pos$1
(= _WRITE_OFFSET_$$pos$1 call2010formal@_offset$2@0))) (and
(or %lbl%@22733 (=> (= (ControlFlow 0 6253) (- 0 22733)) (=> p1$1@1 true)))
(=> (=> p1$1@1 true) (=> (= (ControlFlow 0 6253) 6247) inline$_LOG_WRITE_$$localPos$0$Entry_correct)))))))))
(let ((inline$_LOG_READ_$$pos$7$_LOG_READ_correct (=> (and %lbl%+6167 true) (=> (and
(= _READ_HAS_OCCURRED_$$pos$1@8 (ite (and
p1$1@1
inline$_LOG_READ_$$pos$7$track@1) true _READ_HAS_OCCURRED_$$pos$1@7))
(= _READ_OFFSET_$$pos$1@8 (ite (and
p1$1@1
inline$_LOG_READ_$$pos$7$track@1) inline$_LOG_READ_$$pos$7$_offset$1@1 _READ_OFFSET_$$pos$1@7))
(= _READ_SOURCE_$$pos$1@8 (ite (and
p1$1@1
inline$_LOG_READ_$$pos$7$track@1) #x00000014 _READ_SOURCE_$$pos$1@7))
(= (ControlFlow 0 6167) 6253)) $for.cond$4_correct))))
(let ((inline$_LOG_READ_$$pos$7$Entry_correct (=> (and %lbl%+6165 true) (=> (and
(= inline$_LOG_READ_$$pos$7$_offset$1@1 (bvadd (bvmul (bvadd (bvmul $i.0$1@1 v2$1@0) v0$1@0) #x00000004) #x00000003))
(= (ControlFlow 0 6165) 6167)) inline$_LOG_READ_$$pos$7$_LOG_READ_correct))))
(let (($for.cond$3_correct (=> (and %lbl%+6171 true) (=> (= call1945formal@_offset$2@0 (bvadd (bvmul (bvadd (bvmul $i.0$2@1 v2$2@0) v0$2@0) #x00000004) #x00000002)) (and
(or %lbl%@22572 (=> (= (ControlFlow 0 6171) (- 0 22572)) (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$pos$1
(= _WRITE_OFFSET_$$pos$1 call1945formal@_offset$2@0)))))
(=> (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$pos$1
(= _WRITE_OFFSET_$$pos$1 call1945formal@_offset$2@0))) (and
(or %lbl%@22586 (=> (= (ControlFlow 0 6171) (- 0 22586)) (=> p1$1@1 true)))
(=> (=> p1$1@1 true) (=> (and
(= v11$1@1 (ite p1$1@1 _HAVOC_bv32$1@8 v11$1@0))
(= v11$2@1 (ite p1$2@1 _HAVOC_bv32$2@8 v11$2@0))
(= (ControlFlow 0 6171) 6165)) inline$_LOG_READ_$$pos$7$Entry_correct)))))))))
(let ((inline$_LOG_READ_$$pos$6$_LOG_READ_correct (=> (and %lbl%+6085 true) (=> (and
(= _READ_HAS_OCCURRED_$$pos$1@7 (ite (and
p1$1@1
inline$_LOG_READ_$$pos$6$track@1) true _READ_HAS_OCCURRED_$$pos$1@6))
(= _READ_OFFSET_$$pos$1@7 (ite (and
p1$1@1
inline$_LOG_READ_$$pos$6$track@1) inline$_LOG_READ_$$pos$6$_offset$1@1 _READ_OFFSET_$$pos$1@6))
(= _READ_SOURCE_$$pos$1@7 (ite (and
p1$1@1
inline$_LOG_READ_$$pos$6$track@1) #x00000013 _READ_SOURCE_$$pos$1@6))
(= (ControlFlow 0 6085) 6171)) $for.cond$3_correct))))
(let ((inline$_LOG_READ_$$pos$6$Entry_correct (=> (and %lbl%+6083 true) (=> (and
(= inline$_LOG_READ_$$pos$6$_offset$1@1 (bvadd (bvmul (bvadd (bvmul $i.0$1@1 v2$1@0) v0$1@0) #x00000004) #x00000002))
(= (ControlFlow 0 6083) 6085)) inline$_LOG_READ_$$pos$6$_LOG_READ_correct))))
(let (($for.cond$2_correct (=> (and %lbl%+6089 true) (=> (= call1880formal@_offset$2@0 (bvadd (bvmul (bvadd (bvmul $i.0$2@1 v2$2@0) v0$2@0) #x00000004) #x00000001)) (and
(or %lbl%@22425 (=> (= (ControlFlow 0 6089) (- 0 22425)) (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$pos$1
(= _WRITE_OFFSET_$$pos$1 call1880formal@_offset$2@0)))))
(=> (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$pos$1
(= _WRITE_OFFSET_$$pos$1 call1880formal@_offset$2@0))) (and
(or %lbl%@22439 (=> (= (ControlFlow 0 6089) (- 0 22439)) (=> p1$1@1 true)))
(=> (=> p1$1@1 true) (=> (and
(= v10$1@1 (ite p1$1@1 _HAVOC_bv32$1@7 v10$1@0))
(= v10$2@1 (ite p1$2@1 _HAVOC_bv32$2@7 v10$2@0))
(= (ControlFlow 0 6089) 6083)) inline$_LOG_READ_$$pos$6$Entry_correct)))))))))
(let ((inline$_LOG_READ_$$pos$5$_LOG_READ_correct (=> (and %lbl%+6003 true) (=> (and
(= _READ_HAS_OCCURRED_$$pos$1@6 (ite (and
p1$1@1
inline$_LOG_READ_$$pos$5$track@1) true _READ_HAS_OCCURRED_$$pos$1@5))
(= _READ_OFFSET_$$pos$1@6 (ite (and
p1$1@1
inline$_LOG_READ_$$pos$5$track@1) inline$_LOG_READ_$$pos$5$_offset$1@1 _READ_OFFSET_$$pos$1@5))
(= _READ_SOURCE_$$pos$1@6 (ite (and
p1$1@1
inline$_LOG_READ_$$pos$5$track@1) #x00000012 _READ_SOURCE_$$pos$1@5))
(= (ControlFlow 0 6003) 6089)) $for.cond$2_correct))))
(let ((inline$_LOG_READ_$$pos$5$Entry_correct (=> (and %lbl%+6001 true) (=> (and
(= inline$_LOG_READ_$$pos$5$_offset$1@1 (bvadd (bvmul (bvadd (bvmul $i.0$1@1 v2$1@0) v0$1@0) #x00000004) #x00000001))
(= (ControlFlow 0 6001) 6003)) inline$_LOG_READ_$$pos$5$_LOG_READ_correct))))
(let (($for.cond$1_correct (=> (and %lbl%+6007 true) (=> (= call1815formal@_offset$2@0 (bvmul (bvadd (bvmul $i.0$2@1 v2$2@0) v0$2@0) #x00000004)) (and
(or %lbl%@22278 (=> (= (ControlFlow 0 6007) (- 0 22278)) (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$pos$1
(= _WRITE_OFFSET_$$pos$1 call1815formal@_offset$2@0)))))
(=> (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$pos$1
(= _WRITE_OFFSET_$$pos$1 call1815formal@_offset$2@0))) (and
(or %lbl%@22292 (=> (= (ControlFlow 0 6007) (- 0 22292)) (=> p1$1@1 true)))
(=> (=> p1$1@1 true) (=> (and
(= v9$1@1 (ite p1$1@1 _HAVOC_bv32$1@6 v9$1@0))
(= v9$2@1 (ite p1$2@1 _HAVOC_bv32$2@6 v9$2@0))
(= (ControlFlow 0 6007) 6001)) inline$_LOG_READ_$$pos$5$Entry_correct)))))))))
(let ((inline$_LOG_READ_$$pos$4$_LOG_READ_correct (=> (and %lbl%+5921 true) (=> (and
(= _READ_HAS_OCCURRED_$$pos$1@5 (ite (and
p1$1@1
inline$_LOG_READ_$$pos$4$track@1) true _READ_HAS_OCCURRED_$$pos$1@4))
(= _READ_OFFSET_$$pos$1@5 (ite (and
p1$1@1
inline$_LOG_READ_$$pos$4$track@1) inline$_LOG_READ_$$pos$4$_offset$1@1 _READ_OFFSET_$$pos$1@4))
(= _READ_SOURCE_$$pos$1@5 (ite (and
p1$1@1
inline$_LOG_READ_$$pos$4$track@1) #x00000011 _READ_SOURCE_$$pos$1@4))
(= (ControlFlow 0 5921) 6007)) $for.cond$1_correct))))
(let ((inline$_LOG_READ_$$pos$4$Entry_correct (=> (and %lbl%+5919 true) (=> (and
(= inline$_LOG_READ_$$pos$4$_offset$1@1 (bvmul (bvadd (bvmul $i.0$1@1 v2$1@0) v0$1@0) #x00000004))
(= (ControlFlow 0 5919) 5921)) inline$_LOG_READ_$$pos$4$_LOG_READ_correct))))
(let (($for.cond_correct (=> (and %lbl%+5925 true) (=> (=> _b10 (=> _WRITE_HAS_OCCURRED_$$localPos$1@0 (or
(= _WRITE_OFFSET_$$localPos$1@0 (bvmul local_id_x$1 #x00000004))
(= _WRITE_OFFSET_$$localPos$1@0 (bvadd (bvmul local_id_x$1 #x00000004) #x00000001))
(= _WRITE_OFFSET_$$localPos$1@0 (bvadd (bvmul local_id_x$1 #x00000004) #x00000002))
(= _WRITE_OFFSET_$$localPos$1@0 (bvadd (bvmul local_id_x$1 #x00000004) #x00000003))))) (=> (and
(=> _b9 (=> _READ_HAS_OCCURRED_$$localPos$1@0 (or
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@0) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvmul #x00000000 #x00000004)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@0) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000001)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@0) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000002)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@0) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1@0) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003))))))
(=> _b8 (not _WRITE_HAS_OCCURRED_$$localPos$1@0))) (=> (and
(=> _b7 (not _READ_HAS_OCCURRED_$$localPos$1@0))
(=> _b6 (=> _READ_HAS_OCCURRED_$$pos$1@4 (or
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@4) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004)))
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@4) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvadd (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004) #x00000001)))
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@4) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvadd (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004) #x00000002)))
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@4) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvadd (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004) #x00000003))))))
(=> _b5 (not _READ_HAS_OCCURRED_$$pos$1@4))
(=> _b4 (=> (and
p0$1@1
p0$2@1) (= $j.0$1@0 $j.0$2@0)))) (=> (and
(=> _b3 (=> (and
p0$1@1
p0$2@1) (= $acc.1$1@0 $acc.1$2@0)))
(=> _b2 (=> (and
p0$1@1
p0$2@1) (= $i.0$1@1 $i.0$2@1)))
(=> _b1 (=> (and
p0$1@1
p0$2@1) (= $acc.0$1@1 $acc.0$2@1)))
(=> _b0 (= p0$1@1 p0$2@1))
(=> _READ_HAS_OCCURRED_$$vel$1 (or
(= _READ_SOURCE_$$vel$1 #x00000005)
(= _READ_SOURCE_$$vel$1 #x00000006)
(= _READ_SOURCE_$$vel$1 #x00000007)
(= _READ_SOURCE_$$vel$1 #x00000008)))
(=> _WRITE_HAS_OCCURRED_$$vel$1 false)
(=> (not _READ_HAS_OCCURRED_$$vel$1) (= _READ_SOURCE_$$vel$1 #x00000000))
(=> (not _WRITE_HAS_OCCURRED_$$vel$1) (= _WRITE_SOURCE_$$vel$1 #x00000000))
(=> _READ_HAS_OCCURRED_$$pos$1@4 (or
(= _READ_SOURCE_$$pos$1@4 #x00000001)
(= _READ_SOURCE_$$pos$1@4 #x00000002)
(= _READ_SOURCE_$$pos$1@4 #x00000003)
(= _READ_SOURCE_$$pos$1@4 #x00000004)
(= _READ_SOURCE_$$pos$1@4 #x00000011)
(= _READ_SOURCE_$$pos$1@4 #x00000012)
(= _READ_SOURCE_$$pos$1@4 #x00000013)
(= _READ_SOURCE_$$pos$1@4 #x00000014)))
(=> _WRITE_HAS_OCCURRED_$$pos$1 false)
(=> (not _READ_HAS_OCCURRED_$$pos$1@4) (= _READ_SOURCE_$$pos$1@4 #x00000000))
(=> (not _WRITE_HAS_OCCURRED_$$pos$1) (= _WRITE_SOURCE_$$pos$1 #x00000000))
(=> _READ_HAS_OCCURRED_$$localPos$1@0 (or
(= _READ_SOURCE_$$localPos$1@0 #x00000019)
(= _READ_SOURCE_$$localPos$1@0 #x0000001a)
(= _READ_SOURCE_$$localPos$1@0 #x0000001b)
(= _READ_SOURCE_$$localPos$1@0 #x0000001c)
(= _READ_SOURCE_$$localPos$1@0 #x0000001d)))
(=> _WRITE_HAS_OCCURRED_$$localPos$1@0 (or
(= _WRITE_SOURCE_$$localPos$1@0 #x00000015)
(= _WRITE_SOURCE_$$localPos$1@0 #x00000016)
(= _WRITE_SOURCE_$$localPos$1@0 #x00000017)
(= _WRITE_SOURCE_$$localPos$1@0 #x00000018)))
(=> (not _READ_HAS_OCCURRED_$$localPos$1@0) (= _READ_SOURCE_$$localPos$1@0 #x00000000))
(=> (not _WRITE_HAS_OCCURRED_$$localPos$1@0) (= _WRITE_SOURCE_$$localPos$1@0 #x00000000))
(=> _READ_HAS_OCCURRED_$$newVelocity$1 false)
(=> _WRITE_HAS_OCCURRED_$$newVelocity$1 (or
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000d)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000e)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000f)
(= _WRITE_SOURCE_$$newVelocity$1 #x00000010)))
(=> (not _READ_HAS_OCCURRED_$$newVelocity$1) (= _READ_SOURCE_$$newVelocity$1 #x00000000))
(=> (not _WRITE_HAS_OCCURRED_$$newVelocity$1) (= _WRITE_SOURCE_$$newVelocity$1 #x00000000))
(=> _READ_HAS_OCCURRED_$$newPosition$1 false)
(=> _WRITE_HAS_OCCURRED_$$newPosition$1 (or
(= _WRITE_SOURCE_$$newPosition$1 #x00000009)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000a)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000b)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000c)))
(=> (not _READ_HAS_OCCURRED_$$newPosition$1) (= _READ_SOURCE_$$newPosition$1 #x00000000))
(=> (not _WRITE_HAS_OCCURRED_$$newPosition$1) (= _WRITE_SOURCE_$$newPosition$1 #x00000000))
(=> p0$1@1 _P$1)
(=> p0$2@1 _P$2)
(= v7$1@1 (ite p0$1@1 (bvult $i.0$1@1 (bvudiv $numBodies$1 v2$1@0)) v7$1@0))
(= v7$2@1 (ite p0$2@1 (bvult $i.0$2@1 (bvudiv $numBodies$2 v2$2@0)) v7$2@0))
(= p1$1@1 (ite p0$1@1 v7$1@1 false))
(= p1$2@1 (ite p0$2@1 v7$2@1 false))
(= p0$1@2 (ite p0$1@1 v7$1@1 p0$1@1))
(= p0$2@2 (ite p0$2@1 v7$2@1 p0$2@1))) (and
(or %lbl%@22153 (=> (= (ControlFlow 0 5925) (- 0 22153)) (=> p1$1@1 true)))
(=> (=> p1$1@1 true) (=> (and
(= v8$1@1 (ite p1$1@1 _HAVOC_bv32$1@5 v8$1@0))
(= v8$2@1 (ite p1$2@1 _HAVOC_bv32$2@5 v8$2@0))
(= (ControlFlow 0 5925) 5919)) inline$_LOG_READ_$$pos$4$Entry_correct))))))))))
(let (($entry$4_correct (=> (and %lbl%+5843 true) (=> (= call1006formal@_offset$2@0 (bvadd (bvmul v1$2@0 #x00000004) #x00000003)) (and
(or %lbl%@19579 (=> (= (ControlFlow 0 5843) (- 0 19579)) (not (and
_P$2
_WRITE_HAS_OCCURRED_$$pos$1
(= _WRITE_OFFSET_$$pos$1 call1006formal@_offset$2@0)))))
(=> (not (and
_P$2
_WRITE_HAS_OCCURRED_$$pos$1
(= _WRITE_OFFSET_$$pos$1 call1006formal@_offset$2@0))) (=> (and
(= $acc.0$1@0 (ite _P$1 #x00000000000000000000000000000000 $acc.0$1))
(= $acc.0$2@0 (ite _P$2 #x00000000000000000000000000000000 $acc.0$2))
(= $i.0$1@0 (ite _P$1 #x00000000 $i.0$1))
(= $i.0$2@0 (ite _P$2 #x00000000 $i.0$2))
(= p0$1@0 (ite _P$1 true false))
(= p0$2@0 (ite _P$2 true false))) (and
(or %lbl%@19676 (=> (= (ControlFlow 0 5843) (- 0 19676)) (=> _b10 (=> _WRITE_HAS_OCCURRED_$$localPos$1 (or
(= _WRITE_OFFSET_$$localPos$1 (bvmul local_id_x$1 #x00000004))
(= _WRITE_OFFSET_$$localPos$1 (bvadd (bvmul local_id_x$1 #x00000004) #x00000001))
(= _WRITE_OFFSET_$$localPos$1 (bvadd (bvmul local_id_x$1 #x00000004) #x00000002))
(= _WRITE_OFFSET_$$localPos$1 (bvadd (bvmul local_id_x$1 #x00000004) #x00000003)))))))
(=> (=> _b10 (=> _WRITE_HAS_OCCURRED_$$localPos$1 (or
(= _WRITE_OFFSET_$$localPos$1 (bvmul local_id_x$1 #x00000004))
(= _WRITE_OFFSET_$$localPos$1 (bvadd (bvmul local_id_x$1 #x00000004) #x00000001))
(= _WRITE_OFFSET_$$localPos$1 (bvadd (bvmul local_id_x$1 #x00000004) #x00000002))
(= _WRITE_OFFSET_$$localPos$1 (bvadd (bvmul local_id_x$1 #x00000004) #x00000003))))) (and
(or %lbl%@19742 (=> (= (ControlFlow 0 5843) (- 0 19742)) (=> _b9 (=> _READ_HAS_OCCURRED_$$localPos$1 (or
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvmul #x00000000 #x00000004)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000001)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000002)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003))))))))
(=> (=> _b9 (=> _READ_HAS_OCCURRED_$$localPos$1 (or
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvmul #x00000000 #x00000004)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000001)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000002)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003)))
(= (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) _READ_OFFSET_$$localPos$1) (bvand (bvsub (bvmul #x00000001 #x00000004) #x00000001) (bvadd (bvmul #x00000000 #x00000004) #x00000003)))))) (and
(or %lbl%@19944 (=> (= (ControlFlow 0 5843) (- 0 19944)) (=> _b8 (not _WRITE_HAS_OCCURRED_$$localPos$1))))
(=> (=> _b8 (not _WRITE_HAS_OCCURRED_$$localPos$1)) (and
(or %lbl%@19952 (=> (= (ControlFlow 0 5843) (- 0 19952)) (=> _b7 (not _READ_HAS_OCCURRED_$$localPos$1))))
(=> (=> _b7 (not _READ_HAS_OCCURRED_$$localPos$1)) (and
(or %lbl%@19960 (=> (= (ControlFlow 0 5843) (- 0 19960)) (=> _b6 (=> _READ_HAS_OCCURRED_$$pos$1@3 (or
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@3) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004)))
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@3) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvadd (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004) #x00000001)))
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@3) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvadd (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004) #x00000002)))
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@3) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvadd (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004) #x00000003))))))))
(=> (=> _b6 (=> _READ_HAS_OCCURRED_$$pos$1@3 (or
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@3) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004)))
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@3) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvadd (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004) #x00000001)))
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@3) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvadd (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004) #x00000002)))
(= (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) _READ_OFFSET_$$pos$1@3) (bvand (bvsub (bvmul (bvmul #x00000001 group_size_x) #x00000004) #x00000001) (bvadd (bvmul (bvadd (bvmul #x00000000 group_size_x) local_id_x$1) #x00000004) #x00000003)))))) (and
(or %lbl%@20181 (=> (= (ControlFlow 0 5843) (- 0 20181)) (=> _b5 (not _READ_HAS_OCCURRED_$$pos$1@3))))
(=> (=> _b5 (not _READ_HAS_OCCURRED_$$pos$1@3)) (and
(or %lbl%@20188 (=> (= (ControlFlow 0 5843) (- 0 20188)) (=> _b4 (=> (and
p0$1@0
p0$2@0) (= $j.0$1 $j.0$2)))))
(=> (=> _b4 (=> (and
p0$1@0
p0$2@0) (= $j.0$1 $j.0$2))) (and
(or %lbl%@20204 (=> (= (ControlFlow 0 5843) (- 0 20204)) (=> _b3 (=> (and
p0$1@0
p0$2@0) (= $acc.1$1 $acc.1$2)))))
(=> (=> _b3 (=> (and
p0$1@0
p0$2@0) (= $acc.1$1 $acc.1$2))) (and
(or %lbl%@20220 (=> (= (ControlFlow 0 5843) (- 0 20220)) (=> _b2 (=> (and
p0$1@0
p0$2@0) (= $i.0$1@0 $i.0$2@0)))))
(=> (=> _b2 (=> (and
p0$1@0
p0$2@0) (= $i.0$1@0 $i.0$2@0))) (and
(or %lbl%@20234 (=> (= (ControlFlow 0 5843) (- 0 20234)) (=> _b1 (=> (and
p0$1@0
p0$2@0) (= $acc.0$1@0 $acc.0$2@0)))))
(=> (=> _b1 (=> (and
p0$1@0
p0$2@0) (= $acc.0$1@0 $acc.0$2@0))) (and
(or %lbl%@20248 (=> (= (ControlFlow 0 5843) (- 0 20248)) (=> _b0 (= p0$1@0 p0$2@0))))
(=> (=> _b0 (= p0$1@0 p0$2@0)) (and
(or %lbl%@20256 (=> (= (ControlFlow 0 5843) (- 0 20256)) (=> _READ_HAS_OCCURRED_$$vel$1 (or
(= _READ_SOURCE_$$vel$1 #x00000005)
(= _READ_SOURCE_$$vel$1 #x00000006)
(= _READ_SOURCE_$$vel$1 #x00000007)
(= _READ_SOURCE_$$vel$1 #x00000008)))))
(=> (=> _READ_HAS_OCCURRED_$$vel$1 (or
(= _READ_SOURCE_$$vel$1 #x00000005)
(= _READ_SOURCE_$$vel$1 #x00000006)
(= _READ_SOURCE_$$vel$1 #x00000007)
(= _READ_SOURCE_$$vel$1 #x00000008))) (and
(or %lbl%@20290 (=> (= (ControlFlow 0 5843) (- 0 20290)) (=> _WRITE_HAS_OCCURRED_$$vel$1 false)))
(=> (=> _WRITE_HAS_OCCURRED_$$vel$1 false) (and
(or %lbl%@20296 (=> (= (ControlFlow 0 5843) (- 0 20296)) (=> (not _READ_HAS_OCCURRED_$$vel$1) (= _READ_SOURCE_$$vel$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$vel$1) (= _READ_SOURCE_$$vel$1 #x00000000)) (and
(or %lbl%@20308 (=> (= (ControlFlow 0 5843) (- 0 20308)) (=> (not _WRITE_HAS_OCCURRED_$$vel$1) (= _WRITE_SOURCE_$$vel$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$vel$1) (= _WRITE_SOURCE_$$vel$1 #x00000000)) (and
(or %lbl%@20320 (=> (= (ControlFlow 0 5843) (- 0 20320)) (=> _READ_HAS_OCCURRED_$$pos$1@3 (or
(= _READ_SOURCE_$$pos$1@3 #x00000001)
(= _READ_SOURCE_$$pos$1@3 #x00000002)
(= _READ_SOURCE_$$pos$1@3 #x00000003)
(= _READ_SOURCE_$$pos$1@3 #x00000004)
(= _READ_SOURCE_$$pos$1@3 #x00000011)
(= _READ_SOURCE_$$pos$1@3 #x00000012)
(= _READ_SOURCE_$$pos$1@3 #x00000013)
(= _READ_SOURCE_$$pos$1@3 #x00000014)))))
(=> (=> _READ_HAS_OCCURRED_$$pos$1@3 (or
(= _READ_SOURCE_$$pos$1@3 #x00000001)
(= _READ_SOURCE_$$pos$1@3 #x00000002)
(= _READ_SOURCE_$$pos$1@3 #x00000003)
(= _READ_SOURCE_$$pos$1@3 #x00000004)
(= _READ_SOURCE_$$pos$1@3 #x00000011)
(= _READ_SOURCE_$$pos$1@3 #x00000012)
(= _READ_SOURCE_$$pos$1@3 #x00000013)
(= _READ_SOURCE_$$pos$1@3 #x00000014))) (and
(or %lbl%@20377 (=> (= (ControlFlow 0 5843) (- 0 20377)) (=> _WRITE_HAS_OCCURRED_$$pos$1 false)))
(=> (=> _WRITE_HAS_OCCURRED_$$pos$1 false) (and
(or %lbl%@20383 (=> (= (ControlFlow 0 5843) (- 0 20383)) (=> (not _READ_HAS_OCCURRED_$$pos$1@3) (= _READ_SOURCE_$$pos$1@3 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$pos$1@3) (= _READ_SOURCE_$$pos$1@3 #x00000000)) (and
(or %lbl%@20393 (=> (= (ControlFlow 0 5843) (- 0 20393)) (=> (not _WRITE_HAS_OCCURRED_$$pos$1) (= _WRITE_SOURCE_$$pos$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$pos$1) (= _WRITE_SOURCE_$$pos$1 #x00000000)) (and
(or %lbl%@20405 (=> (= (ControlFlow 0 5843) (- 0 20405)) (=> _READ_HAS_OCCURRED_$$localPos$1 (or
(= _READ_SOURCE_$$localPos$1 #x00000019)
(= _READ_SOURCE_$$localPos$1 #x0000001a)
(= _READ_SOURCE_$$localPos$1 #x0000001b)
(= _READ_SOURCE_$$localPos$1 #x0000001c)
(= _READ_SOURCE_$$localPos$1 #x0000001d)))))
(=> (=> _READ_HAS_OCCURRED_$$localPos$1 (or
(= _READ_SOURCE_$$localPos$1 #x00000019)
(= _READ_SOURCE_$$localPos$1 #x0000001a)
(= _READ_SOURCE_$$localPos$1 #x0000001b)
(= _READ_SOURCE_$$localPos$1 #x0000001c)
(= _READ_SOURCE_$$localPos$1 #x0000001d))) (and
(or %lbl%@20447 (=> (= (ControlFlow 0 5843) (- 0 20447)) (=> _WRITE_HAS_OCCURRED_$$localPos$1 (or
(= _WRITE_SOURCE_$$localPos$1 #x00000015)
(= _WRITE_SOURCE_$$localPos$1 #x00000016)
(= _WRITE_SOURCE_$$localPos$1 #x00000017)
(= _WRITE_SOURCE_$$localPos$1 #x00000018)))))
(=> (=> _WRITE_HAS_OCCURRED_$$localPos$1 (or
(= _WRITE_SOURCE_$$localPos$1 #x00000015)
(= _WRITE_SOURCE_$$localPos$1 #x00000016)
(= _WRITE_SOURCE_$$localPos$1 #x00000017)
(= _WRITE_SOURCE_$$localPos$1 #x00000018))) (and
(or %lbl%@20481 (=> (= (ControlFlow 0 5843) (- 0 20481)) (=> (not _READ_HAS_OCCURRED_$$localPos$1) (= _READ_SOURCE_$$localPos$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$localPos$1) (= _READ_SOURCE_$$localPos$1 #x00000000)) (and
(or %lbl%@20493 (=> (= (ControlFlow 0 5843) (- 0 20493)) (=> (not _WRITE_HAS_OCCURRED_$$localPos$1) (= _WRITE_SOURCE_$$localPos$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$localPos$1) (= _WRITE_SOURCE_$$localPos$1 #x00000000)) (and
(or %lbl%@20505 (=> (= (ControlFlow 0 5843) (- 0 20505)) (=> _READ_HAS_OCCURRED_$$newVelocity$1 false)))
(=> (=> _READ_HAS_OCCURRED_$$newVelocity$1 false) (and
(or %lbl%@20511 (=> (= (ControlFlow 0 5843) (- 0 20511)) (=> _WRITE_HAS_OCCURRED_$$newVelocity$1 (or
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000d)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000e)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000f)
(= _WRITE_SOURCE_$$newVelocity$1 #x00000010)))))
(=> (=> _WRITE_HAS_OCCURRED_$$newVelocity$1 (or
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000d)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000e)
(= _WRITE_SOURCE_$$newVelocity$1 #x0000000f)
(= _WRITE_SOURCE_$$newVelocity$1 #x00000010))) (and
(or %lbl%@20545 (=> (= (ControlFlow 0 5843) (- 0 20545)) (=> (not _READ_HAS_OCCURRED_$$newVelocity$1) (= _READ_SOURCE_$$newVelocity$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$newVelocity$1) (= _READ_SOURCE_$$newVelocity$1 #x00000000)) (and
(or %lbl%@20557 (=> (= (ControlFlow 0 5843) (- 0 20557)) (=> (not _WRITE_HAS_OCCURRED_$$newVelocity$1) (= _WRITE_SOURCE_$$newVelocity$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$newVelocity$1) (= _WRITE_SOURCE_$$newVelocity$1 #x00000000)) (and
(or %lbl%@20569 (=> (= (ControlFlow 0 5843) (- 0 20569)) (=> _READ_HAS_OCCURRED_$$newPosition$1 false)))
(=> (=> _READ_HAS_OCCURRED_$$newPosition$1 false) (and
(or %lbl%@20575 (=> (= (ControlFlow 0 5843) (- 0 20575)) (=> _WRITE_HAS_OCCURRED_$$newPosition$1 (or
(= _WRITE_SOURCE_$$newPosition$1 #x00000009)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000a)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000b)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000c)))))
(=> (=> _WRITE_HAS_OCCURRED_$$newPosition$1 (or
(= _WRITE_SOURCE_$$newPosition$1 #x00000009)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000a)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000b)
(= _WRITE_SOURCE_$$newPosition$1 #x0000000c))) (and
(or %lbl%@20609 (=> (= (ControlFlow 0 5843) (- 0 20609)) (=> (not _READ_HAS_OCCURRED_$$newPosition$1) (= _READ_SOURCE_$$newPosition$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$newPosition$1) (= _READ_SOURCE_$$newPosition$1 #x00000000)) (and
(or %lbl%@20621 (=> (= (ControlFlow 0 5843) (- 0 20621)) (=> (not _WRITE_HAS_OCCURRED_$$newPosition$1) (= _WRITE_SOURCE_$$newPosition$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$newPosition$1) (= _WRITE_SOURCE_$$newPosition$1 #x00000000)) (and
(or %lbl%@20633 (=> (= (ControlFlow 0 5843) (- 0 20633)) (=> p0$1@0 _P$1)))
(=> (=> p0$1@0 _P$1) (and
(or %lbl%@20638 (=> (= (ControlFlow 0 5843) (- 0 20638)) (=> p0$2@0 _P$2)))
(=> (=> p0$2@0 _P$2) (=> (= (ControlFlow 0 5843) 5925) $for.cond_correct))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(let ((inline$_LOG_READ_$$pos$3$_LOG_READ_correct (=> (and %lbl%+5837 true) (=> (and
(= _READ_HAS_OCCURRED_$$pos$1@3 (ite (and
_P$1
inline$_LOG_READ_$$pos$3$track@0) true _READ_HAS_OCCURRED_$$pos$1@2))
(= _READ_OFFSET_$$pos$1@3 (ite (and
_P$1
inline$_LOG_READ_$$pos$3$track@0) inline$_LOG_READ_$$pos$3$_offset$1@0 _READ_OFFSET_$$pos$1@2))
(= _READ_SOURCE_$$pos$1@3 (ite (and
_P$1
inline$_LOG_READ_$$pos$3$track@0) #x00000004 _READ_SOURCE_$$pos$1@2))
(= (ControlFlow 0 5837) 5843)) $entry$4_correct))))
(let ((inline$_LOG_READ_$$pos$3$Entry_correct (=> (and %lbl%+5835 true) (=> (and
(= inline$_LOG_READ_$$pos$3$_offset$1@0 (bvadd (bvmul v1$1@0 #x00000004) #x00000003))
(= (ControlFlow 0 5835) 5837)) inline$_LOG_READ_$$pos$3$_LOG_READ_correct))))
(let (($entry$3_correct (=> (and %lbl%+5841 true) (=> (= call953formal@_offset$2@0 (bvadd (bvmul v1$2@0 #x00000004) #x00000002)) (and
(or %lbl%@19437 (=> (= (ControlFlow 0 5841) (- 0 19437)) (not (and
_P$2
_WRITE_HAS_OCCURRED_$$pos$1
(= _WRITE_OFFSET_$$pos$1 call953formal@_offset$2@0)))))
(=> (not (and
_P$2
_WRITE_HAS_OCCURRED_$$pos$1
(= _WRITE_OFFSET_$$pos$1 call953formal@_offset$2@0))) (and
(or %lbl%@19451 (=> (= (ControlFlow 0 5841) (- 0 19451)) (=> _P$1 true)))
(=> (=> _P$1 true) (=> (and
(= v6$1@0 (ite _P$1 _HAVOC_bv32$1@3 v6$1))
(= v6$2@0 (ite _P$2 _HAVOC_bv32$2@3 v6$2))
(= (ControlFlow 0 5841) 5835)) inline$_LOG_READ_$$pos$3$Entry_correct)))))))))
(let ((inline$_LOG_READ_$$pos$2$_LOG_READ_correct (=> (and %lbl%+5755 true) (=> (and
(= _READ_HAS_OCCURRED_$$pos$1@2 (ite (and
_P$1
inline$_LOG_READ_$$pos$2$track@0) true _READ_HAS_OCCURRED_$$pos$1@1))
(= _READ_OFFSET_$$pos$1@2 (ite (and
_P$1
inline$_LOG_READ_$$pos$2$track@0) inline$_LOG_READ_$$pos$2$_offset$1@0 _READ_OFFSET_$$pos$1@1))
(= _READ_SOURCE_$$pos$1@2 (ite (and
_P$1
inline$_LOG_READ_$$pos$2$track@0) #x00000003 _READ_SOURCE_$$pos$1@1))
(= (ControlFlow 0 5755) 5841)) $entry$3_correct))))
(let ((inline$_LOG_READ_$$pos$2$Entry_correct (=> (and %lbl%+5753 true) (=> (and
(= inline$_LOG_READ_$$pos$2$_offset$1@0 (bvadd (bvmul v1$1@0 #x00000004) #x00000002))
(= (ControlFlow 0 5753) 5755)) inline$_LOG_READ_$$pos$2$_LOG_READ_correct))))
(let (($entry$2_correct (=> (and %lbl%+5759 true) (=> (= call900formal@_offset$2@0 (bvadd (bvmul v1$2@0 #x00000004) #x00000001)) (and
(or %lbl%@19295 (=> (= (ControlFlow 0 5759) (- 0 19295)) (not (and
_P$2
_WRITE_HAS_OCCURRED_$$pos$1
(= _WRITE_OFFSET_$$pos$1 call900formal@_offset$2@0)))))
(=> (not (and
_P$2
_WRITE_HAS_OCCURRED_$$pos$1
(= _WRITE_OFFSET_$$pos$1 call900formal@_offset$2@0))) (and
(or %lbl%@19309 (=> (= (ControlFlow 0 5759) (- 0 19309)) (=> _P$1 true)))
(=> (=> _P$1 true) (=> (and
(= v5$1@0 (ite _P$1 _HAVOC_bv32$1@2 v5$1))
(= v5$2@0 (ite _P$2 _HAVOC_bv32$2@2 v5$2))
(= (ControlFlow 0 5759) 5753)) inline$_LOG_READ_$$pos$2$Entry_correct)))))))))
(let ((inline$_LOG_READ_$$pos$1$_LOG_READ_correct (=> (and %lbl%+5673 true) (=> (and
(= _READ_HAS_OCCURRED_$$pos$1@1 (ite (and
_P$1
inline$_LOG_READ_$$pos$1$track@0) true _READ_HAS_OCCURRED_$$pos$1@0))
(= _READ_OFFSET_$$pos$1@1 (ite (and
_P$1
inline$_LOG_READ_$$pos$1$track@0) inline$_LOG_READ_$$pos$1$_offset$1@0 _READ_OFFSET_$$pos$1@0))
(= _READ_SOURCE_$$pos$1@1 (ite (and
_P$1
inline$_LOG_READ_$$pos$1$track@0) #x00000002 _READ_SOURCE_$$pos$1@0))
(= (ControlFlow 0 5673) 5759)) $entry$2_correct))))
(let ((inline$_LOG_READ_$$pos$1$Entry_correct (=> (and %lbl%+5671 true) (=> (and
(= inline$_LOG_READ_$$pos$1$_offset$1@0 (bvadd (bvmul v1$1@0 #x00000004) #x00000001))
(= (ControlFlow 0 5671) 5673)) inline$_LOG_READ_$$pos$1$_LOG_READ_correct))))
(let (($entry$1_correct (=> (and %lbl%+5677 true) (=> (= call847formal@_offset$2@0 (bvmul v1$2@0 #x00000004)) (and
(or %lbl%@19153 (=> (= (ControlFlow 0 5677) (- 0 19153)) (not (and
_P$2
_WRITE_HAS_OCCURRED_$$pos$1
(= _WRITE_OFFSET_$$pos$1 call847formal@_offset$2@0)))))
(=> (not (and
_P$2
_WRITE_HAS_OCCURRED_$$pos$1
(= _WRITE_OFFSET_$$pos$1 call847formal@_offset$2@0))) (and
(or %lbl%@19167 (=> (= (ControlFlow 0 5677) (- 0 19167)) (=> _P$1 true)))
(=> (=> _P$1 true) (=> (and
(= v4$1@0 (ite _P$1 _HAVOC_bv32$1@1 v4$1))
(= v4$2@0 (ite _P$2 _HAVOC_bv32$2@1 v4$2))
(= (ControlFlow 0 5677) 5671)) inline$_LOG_READ_$$pos$1$Entry_correct)))))))))
(let ((inline$_LOG_READ_$$pos$0$_LOG_READ_correct (=> (and %lbl%+5591 true) (=> (and
(= _READ_HAS_OCCURRED_$$pos$1@0 (ite (and
_P$1
inline$_LOG_READ_$$pos$0$track@0) true _READ_HAS_OCCURRED_$$pos$1))
(= _READ_OFFSET_$$pos$1@0 (ite (and
_P$1
inline$_LOG_READ_$$pos$0$track@0) inline$_LOG_READ_$$pos$0$_offset$1@0 _READ_OFFSET_$$pos$1))
(= _READ_SOURCE_$$pos$1@0 (ite (and
_P$1
inline$_LOG_READ_$$pos$0$track@0) #x00000001 _READ_SOURCE_$$pos$1))
(= (ControlFlow 0 5591) 5677)) $entry$1_correct))))
(let ((inline$_LOG_READ_$$pos$0$Entry_correct (=> (and %lbl%+5589 true) (=> (and
(= inline$_LOG_READ_$$pos$0$_offset$1@0 (bvmul v1$1@0 #x00000004))
(= (ControlFlow 0 5589) 5591)) inline$_LOG_READ_$$pos$0$_LOG_READ_correct))))
(let (($entry_correct (=> (and %lbl%+5595 true) (=> (and
(= v0$1@0 (ite _P$1 local_id_x$1 v0$1))
(= v0$2@0 (ite _P$2 local_id_x$2 v0$2))) (=> (and
(= v1$1@0 (ite _P$1 (bvadd (bvmul group_size_x group_id_x$1) local_id_x$1) v1$1))
(= v1$2@0 (ite _P$2 (bvadd (bvmul group_size_x group_id_x$2) local_id_x$2) v1$2))
(= v2$1@0 (ite _P$1 group_size_x v2$1))
(= v2$2@0 (ite _P$2 group_size_x v2$2))) (and
(or %lbl%@19027 (=> (= (ControlFlow 0 5595) (- 0 19027)) (=> _P$1 true)))
(=> (=> _P$1 true) (=> (and
(= v3$1@0 (ite _P$1 _HAVOC_bv32$1@0 v3$1))
(= v3$2@0 (ite _P$2 _HAVOC_bv32$2@0 v3$2))
(= (ControlFlow 0 5595) 5589)) inline$_LOG_READ_$$pos$0$Entry_correct))))))))
(let ((PreconditionGeneratedEntry_correct (=> (and %lbl%+17409 true) (=> (and
(not _READ_HAS_OCCURRED_$$pos$1)
(not _WRITE_HAS_OCCURRED_$$pos$1)
(= _READ_SOURCE_$$pos$1 #x00000000)
(= _WRITE_SOURCE_$$pos$1 #x00000000)
(not _READ_HAS_OCCURRED_$$vel$1)
(not _WRITE_HAS_OCCURRED_$$vel$1)
(= _READ_SOURCE_$$vel$1 #x00000000)
(= _WRITE_SOURCE_$$vel$1 #x00000000)) (=> (and
(not _READ_HAS_OCCURRED_$$newPosition$1)
(not _WRITE_HAS_OCCURRED_$$newPosition$1)
(= _READ_SOURCE_$$newPosition$1 #x00000000)
(= _WRITE_SOURCE_$$newPosition$1 #x00000000)
(not _READ_HAS_OCCURRED_$$newVelocity$1)
(not _WRITE_HAS_OCCURRED_$$newVelocity$1)
(= _READ_SOURCE_$$newVelocity$1 #x00000000)
(= _WRITE_SOURCE_$$newVelocity$1 #x00000000)
(not _READ_HAS_OCCURRED_$$localPos$1)
(not _WRITE_HAS_OCCURRED_$$localPos$1)
(= _READ_SOURCE_$$localPos$1 #x00000000)
(= _WRITE_SOURCE_$$localPos$1 #x00000000)
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
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (or
(not (= local_id_x$1 local_id_x$2))
(not (= local_id_y$1 local_id_y$2))
(not (= local_id_z$1 local_id_z$2))))
(= _P$1 _P$2)
(= $numBodies$1 $numBodies$2)
(= $deltaTime$1 $deltaTime$2)
(= $epsSqr$1 $epsSqr$2)
(= (ControlFlow 0 17409) 5595)) $entry_correct))))))
PreconditionGeneratedEntry_correct)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(push 1)
;(set-info :boogie-vc-id $nbody_sim)
(assert (not
(=> (and
true
_b0
_b1
_b2
_b3
_b4
_b5
_b6
_b7
_b8
_b9
_b10
_b11) $nbody_sim)
))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 17409)))
;(get-value ((ControlFlow 0 5595)))
;(get-value ((ControlFlow 0 5589)))
;(get-value ((ControlFlow 0 5591)))
;(get-value ((ControlFlow 0 5677)))
;(get-value ((ControlFlow 0 5671)))
;(get-value ((ControlFlow 0 5673)))
;(get-value ((ControlFlow 0 5759)))
;(get-value ((ControlFlow 0 5753)))
;(get-value ((ControlFlow 0 5755)))
;(get-value ((ControlFlow 0 5841)))
;(get-value ((ControlFlow 0 5835)))
;(get-value ((ControlFlow 0 5837)))
;(get-value ((ControlFlow 0 5843)))
(assert (not (= (ControlFlow 0 5843) (- 20181))))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 17409)))
;(get-value ((ControlFlow 0 5595)))
;(get-value ((ControlFlow 0 5589)))
;(get-value ((ControlFlow 0 5591)))
;(get-value ((ControlFlow 0 5677)))
;(get-value ((ControlFlow 0 5671)))
;(get-value ((ControlFlow 0 5673)))
;(get-value ((ControlFlow 0 5759)))
;(get-value ((ControlFlow 0 5753)))
;(get-value ((ControlFlow 0 5755)))
;(get-value ((ControlFlow 0 5841)))
;(get-value ((ControlFlow 0 5835)))
;(get-value ((ControlFlow 0 5837)))
;(get-value ((ControlFlow 0 5843)))
(assert (not (= (ControlFlow 0 5843) (- 20188))))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 17409)))
;(get-value ((ControlFlow 0 5595)))
;(get-value ((ControlFlow 0 5589)))
;(get-value ((ControlFlow 0 5591)))
;(get-value ((ControlFlow 0 5677)))
;(get-value ((ControlFlow 0 5671)))
;(get-value ((ControlFlow 0 5673)))
;(get-value ((ControlFlow 0 5759)))
;(get-value ((ControlFlow 0 5753)))
;(get-value ((ControlFlow 0 5755)))
;(get-value ((ControlFlow 0 5841)))
;(get-value ((ControlFlow 0 5835)))
;(get-value ((ControlFlow 0 5837)))
;(get-value ((ControlFlow 0 5843)))
(assert (not (= (ControlFlow 0 5843) (- 20204))))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 17409)))
;(get-value ((ControlFlow 0 5595)))
;(get-value ((ControlFlow 0 5589)))
;(get-value ((ControlFlow 0 5591)))
;(get-value ((ControlFlow 0 5677)))
;(get-value ((ControlFlow 0 5671)))
;(get-value ((ControlFlow 0 5673)))
;(get-value ((ControlFlow 0 5759)))
;(get-value ((ControlFlow 0 5753)))
;(get-value ((ControlFlow 0 5755)))
;(get-value ((ControlFlow 0 5841)))
;(get-value ((ControlFlow 0 5835)))
;(get-value ((ControlFlow 0 5837)))
;(get-value ((ControlFlow 0 5843)))
;(get-value ((ControlFlow 0 5925)))
;(get-value ((ControlFlow 0 5919)))
;(get-value ((ControlFlow 0 5921)))
;(get-value ((ControlFlow 0 6007)))
;(get-value ((ControlFlow 0 6001)))
;(get-value ((ControlFlow 0 6003)))
;(get-value ((ControlFlow 0 6089)))
;(get-value ((ControlFlow 0 6083)))
;(get-value ((ControlFlow 0 6085)))
;(get-value ((ControlFlow 0 6171)))
;(get-value ((ControlFlow 0 6165)))
;(get-value ((ControlFlow 0 6167)))
;(get-value ((ControlFlow 0 6253)))
;(get-value ((ControlFlow 0 6247)))
;(get-value ((ControlFlow 0 6249)))
;(get-value ((ControlFlow 0 6335)))
;(get-value ((ControlFlow 0 6329)))
;(get-value ((ControlFlow 0 6331)))
;(get-value ((ControlFlow 0 6417)))
;(get-value ((ControlFlow 0 6411)))
;(get-value ((ControlFlow 0 6413)))
;(get-value ((ControlFlow 0 6499)))
;(get-value ((ControlFlow 0 6493)))
;(get-value ((ControlFlow 0 6495)))
;(get-value ((ControlFlow 0 7034)))
;(get-value ((ControlFlow 0 7002)))
;(get-value ((ControlFlow 0 7006)))
;(get-value ((ControlFlow 0 7028)))
;(get-value ((ControlFlow 0 7026)))
;(get-value ((ControlFlow 0 7016)))
;(get-value ((ControlFlow 0 7018)))
;(get-value ((ControlFlow 0 7020)))
;(get-value ((ControlFlow 0 7032)))
;(get-value ((ControlFlow 0 7036)))
;(get-value ((ControlFlow 0 7118)))
;(get-value ((ControlFlow 0 7112)))
;(get-value ((ControlFlow 0 7114)))
;(get-value ((ControlFlow 0 7200)))
;(get-value ((ControlFlow 0 7194)))
;(get-value ((ControlFlow 0 7196)))
;(get-value ((ControlFlow 0 7282)))
;(get-value ((ControlFlow 0 7276)))
;(get-value ((ControlFlow 0 7278)))
;(get-value ((ControlFlow 0 7364)))
;(get-value ((ControlFlow 0 7358)))
;(get-value ((ControlFlow 0 7360)))
;(get-value ((ControlFlow 0 7446)))
;(get-value ((ControlFlow 0 7440)))
;(get-value ((ControlFlow 0 7442)))
;(get-value ((ControlFlow 0 7448)))
;(get-value ((ControlFlow 0 7983)))
;(get-value ((ControlFlow 0 7951)))
;(get-value ((ControlFlow 0 7955)))
;(get-value ((ControlFlow 0 7977)))
;(get-value ((ControlFlow 0 7975)))
;(get-value ((ControlFlow 0 7965)))
;(get-value ((ControlFlow 0 7967)))
;(get-value ((ControlFlow 0 7969)))
;(get-value ((ControlFlow 0 7981)))
;(get-value ((ControlFlow 0 7985)))
;(get-value ((ControlFlow 0 8973)))
(assert (not (= (ControlFlow 0 8973) (- 28090))))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 17409)))
;(get-value ((ControlFlow 0 5595)))
;(get-value ((ControlFlow 0 5589)))
;(get-value ((ControlFlow 0 5591)))
;(get-value ((ControlFlow 0 5677)))
;(get-value ((ControlFlow 0 5671)))
;(get-value ((ControlFlow 0 5673)))
;(get-value ((ControlFlow 0 5759)))
;(get-value ((ControlFlow 0 5753)))
;(get-value ((ControlFlow 0 5755)))
;(get-value ((ControlFlow 0 5841)))
;(get-value ((ControlFlow 0 5835)))
;(get-value ((ControlFlow 0 5837)))
;(get-value ((ControlFlow 0 5843)))
;(get-value ((ControlFlow 0 5925)))
;(get-value ((ControlFlow 0 5919)))
;(get-value ((ControlFlow 0 5921)))
;(get-value ((ControlFlow 0 6007)))
;(get-value ((ControlFlow 0 6001)))
;(get-value ((ControlFlow 0 6003)))
;(get-value ((ControlFlow 0 6089)))
;(get-value ((ControlFlow 0 6083)))
;(get-value ((ControlFlow 0 6085)))
;(get-value ((ControlFlow 0 6171)))
;(get-value ((ControlFlow 0 6165)))
;(get-value ((ControlFlow 0 6167)))
;(get-value ((ControlFlow 0 6253)))
;(get-value ((ControlFlow 0 6247)))
;(get-value ((ControlFlow 0 6249)))
;(get-value ((ControlFlow 0 6335)))
;(get-value ((ControlFlow 0 6329)))
;(get-value ((ControlFlow 0 6331)))
;(get-value ((ControlFlow 0 6417)))
;(get-value ((ControlFlow 0 6411)))
;(get-value ((ControlFlow 0 6413)))
;(get-value ((ControlFlow 0 6499)))
;(get-value ((ControlFlow 0 6493)))
;(get-value ((ControlFlow 0 6495)))
;(get-value ((ControlFlow 0 7034)))
;(get-value ((ControlFlow 0 7002)))
;(get-value ((ControlFlow 0 7006)))
;(get-value ((ControlFlow 0 7028)))
;(get-value ((ControlFlow 0 7026)))
;(get-value ((ControlFlow 0 7016)))
;(get-value ((ControlFlow 0 7018)))
;(get-value ((ControlFlow 0 7020)))
;(get-value ((ControlFlow 0 7032)))
;(get-value ((ControlFlow 0 7036)))
;(get-value ((ControlFlow 0 7118)))
;(get-value ((ControlFlow 0 7112)))
;(get-value ((ControlFlow 0 7114)))
;(get-value ((ControlFlow 0 7200)))
;(get-value ((ControlFlow 0 7194)))
;(get-value ((ControlFlow 0 7196)))
;(get-value ((ControlFlow 0 7282)))
;(get-value ((ControlFlow 0 7276)))
;(get-value ((ControlFlow 0 7278)))
;(get-value ((ControlFlow 0 7364)))
;(get-value ((ControlFlow 0 7358)))
;(get-value ((ControlFlow 0 7360)))
;(get-value ((ControlFlow 0 7446)))
;(get-value ((ControlFlow 0 7440)))
;(get-value ((ControlFlow 0 7442)))
;(get-value ((ControlFlow 0 7448)))
;(get-value ((ControlFlow 0 7983)))
;(get-value ((ControlFlow 0 7951)))
;(get-value ((ControlFlow 0 7955)))
;(get-value ((ControlFlow 0 7977)))
;(get-value ((ControlFlow 0 7975)))
;(get-value ((ControlFlow 0 7965)))
;(get-value ((ControlFlow 0 7967)))
;(get-value ((ControlFlow 0 7969)))
;(get-value ((ControlFlow 0 7981)))
;(get-value ((ControlFlow 0 7985)))
;(get-value ((ControlFlow 0 8973)))
(pop 1)
(push 1)
;(set-info :boogie-vc-id $nbody_sim)
(assert (not
(=> (and
true
_b0
_b1
_b2
(not _b3)
(not _b4)
(not _b5)
_b6
_b7
_b8
_b9
_b10
_b11) $nbody_sim)
))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 17409)))
;(get-value ((ControlFlow 0 5595)))
;(get-value ((ControlFlow 0 5589)))
;(get-value ((ControlFlow 0 5591)))
;(get-value ((ControlFlow 0 5677)))
;(get-value ((ControlFlow 0 5671)))
;(get-value ((ControlFlow 0 5673)))
;(get-value ((ControlFlow 0 5759)))
;(get-value ((ControlFlow 0 5753)))
;(get-value ((ControlFlow 0 5755)))
;(get-value ((ControlFlow 0 5841)))
;(get-value ((ControlFlow 0 5835)))
;(get-value ((ControlFlow 0 5837)))
;(get-value ((ControlFlow 0 5843)))
;(get-value ((ControlFlow 0 5925)))
;(get-value ((ControlFlow 0 5919)))
;(get-value ((ControlFlow 0 5921)))
;(get-value ((ControlFlow 0 6007)))
;(get-value ((ControlFlow 0 6001)))
;(get-value ((ControlFlow 0 6003)))
;(get-value ((ControlFlow 0 6089)))
;(get-value ((ControlFlow 0 6083)))
;(get-value ((ControlFlow 0 6085)))
;(get-value ((ControlFlow 0 6171)))
;(get-value ((ControlFlow 0 6165)))
;(get-value ((ControlFlow 0 6167)))
;(get-value ((ControlFlow 0 6253)))
;(get-value ((ControlFlow 0 6247)))
;(get-value ((ControlFlow 0 6249)))
;(get-value ((ControlFlow 0 6335)))
;(get-value ((ControlFlow 0 6329)))
;(get-value ((ControlFlow 0 6331)))
;(get-value ((ControlFlow 0 6417)))
;(get-value ((ControlFlow 0 6411)))
;(get-value ((ControlFlow 0 6413)))
;(get-value ((ControlFlow 0 6499)))
;(get-value ((ControlFlow 0 6493)))
;(get-value ((ControlFlow 0 6495)))
;(get-value ((ControlFlow 0 7034)))
;(get-value ((ControlFlow 0 7002)))
;(get-value ((ControlFlow 0 7006)))
;(get-value ((ControlFlow 0 7028)))
;(get-value ((ControlFlow 0 7026)))
;(get-value ((ControlFlow 0 7016)))
;(get-value ((ControlFlow 0 7018)))
;(get-value ((ControlFlow 0 7020)))
;(get-value ((ControlFlow 0 7032)))
;(get-value ((ControlFlow 0 7036)))
;(get-value ((ControlFlow 0 7118)))
;(get-value ((ControlFlow 0 7112)))
;(get-value ((ControlFlow 0 7114)))
;(get-value ((ControlFlow 0 7200)))
;(get-value ((ControlFlow 0 7194)))
;(get-value ((ControlFlow 0 7196)))
;(get-value ((ControlFlow 0 7282)))
;(get-value ((ControlFlow 0 7276)))
;(get-value ((ControlFlow 0 7278)))
;(get-value ((ControlFlow 0 7364)))
;(get-value ((ControlFlow 0 7358)))
;(get-value ((ControlFlow 0 7360)))
;(get-value ((ControlFlow 0 7446)))
;(get-value ((ControlFlow 0 7440)))
;(get-value ((ControlFlow 0 7442)))
;(get-value ((ControlFlow 0 7448)))
;(get-value ((ControlFlow 0 7983)))
;(get-value ((ControlFlow 0 7951)))
;(get-value ((ControlFlow 0 7955)))
;(get-value ((ControlFlow 0 7977)))
;(get-value ((ControlFlow 0 7975)))
;(get-value ((ControlFlow 0 7965)))
;(get-value ((ControlFlow 0 7967)))
;(get-value ((ControlFlow 0 7969)))
;(get-value ((ControlFlow 0 7981)))
;(get-value ((ControlFlow 0 7985)))
;(get-value ((ControlFlow 0 8973)))
(assert (not (= (ControlFlow 0 8973) (- 28118))))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 17409)))
;(get-value ((ControlFlow 0 5595)))
;(get-value ((ControlFlow 0 5589)))
;(get-value ((ControlFlow 0 5591)))
;(get-value ((ControlFlow 0 5677)))
;(get-value ((ControlFlow 0 5671)))
;(get-value ((ControlFlow 0 5673)))
;(get-value ((ControlFlow 0 5759)))
;(get-value ((ControlFlow 0 5753)))
;(get-value ((ControlFlow 0 5755)))
;(get-value ((ControlFlow 0 5841)))
;(get-value ((ControlFlow 0 5835)))
;(get-value ((ControlFlow 0 5837)))
;(get-value ((ControlFlow 0 5843)))
;(get-value ((ControlFlow 0 5925)))
;(get-value ((ControlFlow 0 5919)))
;(get-value ((ControlFlow 0 5921)))
;(get-value ((ControlFlow 0 6007)))
;(get-value ((ControlFlow 0 6001)))
;(get-value ((ControlFlow 0 6003)))
;(get-value ((ControlFlow 0 6089)))
;(get-value ((ControlFlow 0 6083)))
;(get-value ((ControlFlow 0 6085)))
;(get-value ((ControlFlow 0 6171)))
;(get-value ((ControlFlow 0 6165)))
;(get-value ((ControlFlow 0 6167)))
;(get-value ((ControlFlow 0 6253)))
;(get-value ((ControlFlow 0 6247)))
;(get-value ((ControlFlow 0 6249)))
;(get-value ((ControlFlow 0 6335)))
;(get-value ((ControlFlow 0 6329)))
;(get-value ((ControlFlow 0 6331)))
;(get-value ((ControlFlow 0 6417)))
;(get-value ((ControlFlow 0 6411)))
;(get-value ((ControlFlow 0 6413)))
;(get-value ((ControlFlow 0 6499)))
;(get-value ((ControlFlow 0 6493)))
;(get-value ((ControlFlow 0 6495)))
;(get-value ((ControlFlow 0 7034)))
;(get-value ((ControlFlow 0 7002)))
;(get-value ((ControlFlow 0 7006)))
;(get-value ((ControlFlow 0 7028)))
;(get-value ((ControlFlow 0 7026)))
;(get-value ((ControlFlow 0 7016)))
;(get-value ((ControlFlow 0 7018)))
;(get-value ((ControlFlow 0 7020)))
;(get-value ((ControlFlow 0 7032)))
;(get-value ((ControlFlow 0 7036)))
;(get-value ((ControlFlow 0 7118)))
;(get-value ((ControlFlow 0 7112)))
;(get-value ((ControlFlow 0 7114)))
;(get-value ((ControlFlow 0 7200)))
;(get-value ((ControlFlow 0 7194)))
;(get-value ((ControlFlow 0 7196)))
;(get-value ((ControlFlow 0 7282)))
;(get-value ((ControlFlow 0 7276)))
;(get-value ((ControlFlow 0 7278)))
;(get-value ((ControlFlow 0 7364)))
;(get-value ((ControlFlow 0 7358)))
;(get-value ((ControlFlow 0 7360)))
;(get-value ((ControlFlow 0 7446)))
;(get-value ((ControlFlow 0 7440)))
;(get-value ((ControlFlow 0 7442)))
;(get-value ((ControlFlow 0 7448)))
;(get-value ((ControlFlow 0 7983)))
;(get-value ((ControlFlow 0 7951)))
;(get-value ((ControlFlow 0 7955)))
;(get-value ((ControlFlow 0 7977)))
;(get-value ((ControlFlow 0 7975)))
;(get-value ((ControlFlow 0 7965)))
;(get-value ((ControlFlow 0 7967)))
;(get-value ((ControlFlow 0 7969)))
;(get-value ((ControlFlow 0 7981)))
;(get-value ((ControlFlow 0 7985)))
;(get-value ((ControlFlow 0 8973)))
(assert (not (= (ControlFlow 0 8973) (- 28132))))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 17409)))
;(get-value ((ControlFlow 0 5595)))
;(get-value ((ControlFlow 0 5589)))
;(get-value ((ControlFlow 0 5591)))
;(get-value ((ControlFlow 0 5677)))
;(get-value ((ControlFlow 0 5671)))
;(get-value ((ControlFlow 0 5673)))
;(get-value ((ControlFlow 0 5759)))
;(get-value ((ControlFlow 0 5753)))
;(get-value ((ControlFlow 0 5755)))
;(get-value ((ControlFlow 0 5841)))
;(get-value ((ControlFlow 0 5835)))
;(get-value ((ControlFlow 0 5837)))
;(get-value ((ControlFlow 0 5843)))
(assert (not (= (ControlFlow 0 5843) (- 20234))))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 17409)))
;(get-value ((ControlFlow 0 5595)))
;(get-value ((ControlFlow 0 5589)))
;(get-value ((ControlFlow 0 5591)))
;(get-value ((ControlFlow 0 5677)))
;(get-value ((ControlFlow 0 5671)))
;(get-value ((ControlFlow 0 5673)))
;(get-value ((ControlFlow 0 5759)))
;(get-value ((ControlFlow 0 5753)))
;(get-value ((ControlFlow 0 5755)))
;(get-value ((ControlFlow 0 5841)))
;(get-value ((ControlFlow 0 5835)))
;(get-value ((ControlFlow 0 5837)))
;(get-value ((ControlFlow 0 5843)))
(assert (not (= (ControlFlow 0 5843) (- 20220))))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 17409)))
;(get-value ((ControlFlow 0 5595)))
;(get-value ((ControlFlow 0 5589)))
;(get-value ((ControlFlow 0 5591)))
;(get-value ((ControlFlow 0 5677)))
;(get-value ((ControlFlow 0 5671)))
;(get-value ((ControlFlow 0 5673)))
;(get-value ((ControlFlow 0 5759)))
;(get-value ((ControlFlow 0 5753)))
;(get-value ((ControlFlow 0 5755)))
;(get-value ((ControlFlow 0 5841)))
;(get-value ((ControlFlow 0 5835)))
;(get-value ((ControlFlow 0 5837)))
;(get-value ((ControlFlow 0 5843)))
(pop 1)
