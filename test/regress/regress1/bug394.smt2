; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
;(set-option :produce-unsat-cores true)
(set-option :print-success false)
(set-info :smt-lib-version 2.0)
;(set-option :produce-models true)
(set-logic ALL_SUPPORTED)
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

(declare-fun group_size_z () (_ BitVec 32))
(declare-fun num_groups_z () (_ BitVec 32))
(declare-fun group_size_x () (_ BitVec 32))
(declare-fun group_size_y () (_ BitVec 32))
(declare-fun num_groups_x () (_ BitVec 32))
(declare-fun num_groups_y () (_ BitVec 32))
(declare-fun ControlFlow (Int Int) Int)
(declare-fun %lbl%+823 () Bool)
(declare-fun $ret$1@0 () (_ BitVec 32))
(declare-fun _P$1 () Bool)
(declare-fun $blockIdy$1 () (_ BitVec 32))
(declare-fun $blockWidth$1 () (_ BitVec 32))
(declare-fun $localIdy$1 () (_ BitVec 32))
(declare-fun $globalWidth$1 () (_ BitVec 32))
(declare-fun $blockIdx$1 () (_ BitVec 32))
(declare-fun $localIdx$1 () (_ BitVec 32))
(declare-fun $ret$1 () (_ BitVec 32))
(declare-fun $ret$2@0 () (_ BitVec 32))
(declare-fun _P$2 () Bool)
(declare-fun $blockIdy$2 () (_ BitVec 32))
(declare-fun $blockWidth$2 () (_ BitVec 32))
(declare-fun $localIdy$2 () (_ BitVec 32))
(declare-fun $globalWidth$2 () (_ BitVec 32))
(declare-fun $blockIdx$2 () (_ BitVec 32))
(declare-fun $localIdx$2 () (_ BitVec 32))
(declare-fun $ret$2 () (_ BitVec 32))
(declare-fun %lbl%@10729 () Bool)
(declare-fun _b29 () Bool)
(declare-fun %lbl%@10737 () Bool)
(declare-fun _b30 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$output$1 () Bool)
(declare-fun %lbl%@10745 () Bool)
(declare-fun _b31 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$output$1 () Bool)
(declare-fun %lbl%@10753 () Bool)
(declare-fun _b32 () Bool)
(declare-fun _WRITE_OFFSET_$$output$1 () (_ BitVec 32))
(declare-fun local_id_x$1 () (_ BitVec 32))
(declare-fun %lbl%@10767 () Bool)
(declare-fun _b33 () Bool)
(declare-fun _READ_OFFSET_$$output$1 () (_ BitVec 32))
(declare-fun %lbl%@10781 () Bool)
(declare-fun _b34 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$input$1 () Bool)
(declare-fun %lbl%@10789 () Bool)
(declare-fun _b35 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$input$1 () Bool)
(declare-fun %lbl%@10797 () Bool)
(declare-fun _b36 () Bool)
(declare-fun _WRITE_OFFSET_$$input$1 () (_ BitVec 32))
(declare-fun %lbl%@10811 () Bool)
(declare-fun _b37 () Bool)
(declare-fun _READ_OFFSET_$$input$1 () (_ BitVec 32))
(declare-fun %lbl%@10825 () Bool)
(declare-fun _b38 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$dct8x8$1 () Bool)
(declare-fun %lbl%@10833 () Bool)
(declare-fun _b39 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$dct8x8$1 () Bool)
(declare-fun %lbl%@10841 () Bool)
(declare-fun _b40 () Bool)
(declare-fun _WRITE_OFFSET_$$dct8x8$1 () (_ BitVec 32))
(declare-fun %lbl%@10855 () Bool)
(declare-fun _b41 () Bool)
(declare-fun _READ_OFFSET_$$dct8x8$1 () (_ BitVec 32))
(declare-fun %lbl%@10869 () Bool)
(declare-fun _b42 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$inter$1 () Bool)
(declare-fun %lbl%@10877 () Bool)
(declare-fun _b43 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$inter$1 () Bool)
(declare-fun %lbl%@10885 () Bool)
(declare-fun _b44 () Bool)
(declare-fun _WRITE_OFFSET_$$inter$1 () (_ BitVec 32))
(declare-fun %lbl%@10899 () Bool)
(declare-fun _b45 () Bool)
(declare-fun _READ_OFFSET_$$inter$1 () (_ BitVec 32))
(declare-fun %lbl%+9318 () Bool)
(declare-fun group_id_x$1 () (_ BitVec 32))
(declare-fun group_id_x$2 () (_ BitVec 32))
(declare-fun local_id_x$2 () (_ BitVec 32))
(declare-fun group_id_y$1 () (_ BitVec 32))
(declare-fun group_id_y$2 () (_ BitVec 32))
(declare-fun local_id_y$1 () (_ BitVec 32))
(declare-fun local_id_y$2 () (_ BitVec 32))
(declare-fun group_id_z$1 () (_ BitVec 32))
(declare-fun group_id_z$2 () (_ BitVec 32))
(declare-fun local_id_z$1 () (_ BitVec 32))
(declare-fun local_id_z$2 () (_ BitVec 32))
(declare-fun _b0 () Bool)
(declare-fun _b1 () Bool)
(declare-fun _b2 () Bool)
(declare-fun _b3 () Bool)
(declare-fun _b4 () Bool)
(declare-fun _b5 () Bool)
(declare-fun _b6 () Bool)
(declare-fun _b7 () Bool)
(declare-fun _b8 () Bool)
(declare-fun _b9 () Bool)
(declare-fun _b10 () Bool)
(declare-fun _b11 () Bool)
(declare-fun _b12 () Bool)
(declare-fun _b13 () Bool)
(declare-fun _b14 () Bool)
(declare-fun _b15 () Bool)
(declare-fun _b16 () Bool)
(declare-fun _b17 () Bool)
(declare-fun _b18 () Bool)
(declare-fun _b19 () Bool)
(declare-fun _b20 () Bool)
(declare-fun _b21 () Bool)
(declare-fun _b22 () Bool)
(declare-fun _b23 () Bool)
(declare-fun _b24 () Bool)
(declare-fun _b25 () Bool)
(declare-fun _b26 () Bool)
(declare-fun _b27 () Bool)
(declare-fun _b28 () Bool)
(assert (not (= (ite (= group_size_z #x00000001) #b1 #b0) #b0)))
(assert (not (= (ite (= num_groups_z #x00000001) #b1 #b0) #b0)))
(assert (not (= (ite (= group_size_x #x00000008) #b1 #b0) #b0)))
(assert (not (= (ite (= group_size_y #x00000008) #b1 #b0) #b0)))
(assert (not (= (ite (= num_groups_x #x00000008) #b1 #b0) #b0)))
(assert (not (= (ite (= num_groups_y #x00000008) #b1 #b0) #b0)))
(define-fun $getIdx () Bool (=> (= (ControlFlow 0 0) 9318) (let (($entry_correct (=> (and %lbl%+823 true) (=> (and
(= $ret$1@0 (ite _P$1 (bvadd (bvmul (bvadd (bvmul $blockIdy$1 $blockWidth$1) $localIdy$1) $globalWidth$1) (bvadd (bvmul $blockIdx$1 $blockWidth$1) $localIdx$1)) $ret$1))
(= $ret$2@0 (ite _P$2 (bvadd (bvmul (bvadd (bvmul $blockIdy$2 $blockWidth$2) $localIdy$2) $globalWidth$2) (bvadd (bvmul $blockIdx$2 $blockWidth$2) $localIdx$2)) $ret$2))) (and
(or %lbl%@10729 (=> (= (ControlFlow 0 823) (- 0 10729)) (=> _b29 (= $ret$1@0 $ret$2@0))))
(=> (=> _b29 (= $ret$1@0 $ret$2@0)) (and
(or %lbl%@10737 (=> (= (ControlFlow 0 823) (- 0 10737)) (=> _b30 (not _READ_HAS_OCCURRED_$$output$1))))
(=> (=> _b30 (not _READ_HAS_OCCURRED_$$output$1)) (and
(or %lbl%@10745 (=> (= (ControlFlow 0 823) (- 0 10745)) (=> _b31 (not _WRITE_HAS_OCCURRED_$$output$1))))
(=> (=> _b31 (not _WRITE_HAS_OCCURRED_$$output$1)) (and
(or %lbl%@10753 (=> (= (ControlFlow 0 823) (- 0 10753)) (=> _b32 (=> _WRITE_HAS_OCCURRED_$$output$1 (= _WRITE_OFFSET_$$output$1 local_id_x$1)))))
(=> (=> _b32 (=> _WRITE_HAS_OCCURRED_$$output$1 (= _WRITE_OFFSET_$$output$1 local_id_x$1))) (and
(or %lbl%@10767 (=> (= (ControlFlow 0 823) (- 0 10767)) (=> _b33 (=> _READ_HAS_OCCURRED_$$output$1 (= _READ_OFFSET_$$output$1 local_id_x$1)))))
(=> (=> _b33 (=> _READ_HAS_OCCURRED_$$output$1 (= _READ_OFFSET_$$output$1 local_id_x$1))) (and
(or %lbl%@10781 (=> (= (ControlFlow 0 823) (- 0 10781)) (=> _b34 (not _READ_HAS_OCCURRED_$$input$1))))
(=> (=> _b34 (not _READ_HAS_OCCURRED_$$input$1)) (and
(or %lbl%@10789 (=> (= (ControlFlow 0 823) (- 0 10789)) (=> _b35 (not _WRITE_HAS_OCCURRED_$$input$1))))
(=> (=> _b35 (not _WRITE_HAS_OCCURRED_$$input$1)) (and
(or %lbl%@10797 (=> (= (ControlFlow 0 823) (- 0 10797)) (=> _b36 (=> _WRITE_HAS_OCCURRED_$$input$1 (= _WRITE_OFFSET_$$input$1 local_id_x$1)))))
(=> (=> _b36 (=> _WRITE_HAS_OCCURRED_$$input$1 (= _WRITE_OFFSET_$$input$1 local_id_x$1))) (and
(or %lbl%@10811 (=> (= (ControlFlow 0 823) (- 0 10811)) (=> _b37 (=> _READ_HAS_OCCURRED_$$input$1 (= _READ_OFFSET_$$input$1 local_id_x$1)))))
(=> (=> _b37 (=> _READ_HAS_OCCURRED_$$input$1 (= _READ_OFFSET_$$input$1 local_id_x$1))) (and
(or %lbl%@10825 (=> (= (ControlFlow 0 823) (- 0 10825)) (=> _b38 (not _READ_HAS_OCCURRED_$$dct8x8$1))))
(=> (=> _b38 (not _READ_HAS_OCCURRED_$$dct8x8$1)) (and
(or %lbl%@10833 (=> (= (ControlFlow 0 823) (- 0 10833)) (=> _b39 (not _WRITE_HAS_OCCURRED_$$dct8x8$1))))
(=> (=> _b39 (not _WRITE_HAS_OCCURRED_$$dct8x8$1)) (and
(or %lbl%@10841 (=> (= (ControlFlow 0 823) (- 0 10841)) (=> _b40 (=> _WRITE_HAS_OCCURRED_$$dct8x8$1 (= _WRITE_OFFSET_$$dct8x8$1 local_id_x$1)))))
(=> (=> _b40 (=> _WRITE_HAS_OCCURRED_$$dct8x8$1 (= _WRITE_OFFSET_$$dct8x8$1 local_id_x$1))) (and
(or %lbl%@10855 (=> (= (ControlFlow 0 823) (- 0 10855)) (=> _b41 (=> _READ_HAS_OCCURRED_$$dct8x8$1 (= _READ_OFFSET_$$dct8x8$1 local_id_x$1)))))
(=> (=> _b41 (=> _READ_HAS_OCCURRED_$$dct8x8$1 (= _READ_OFFSET_$$dct8x8$1 local_id_x$1))) (and
(or %lbl%@10869 (=> (= (ControlFlow 0 823) (- 0 10869)) (=> _b42 (not _READ_HAS_OCCURRED_$$inter$1))))
(=> (=> _b42 (not _READ_HAS_OCCURRED_$$inter$1)) (and
(or %lbl%@10877 (=> (= (ControlFlow 0 823) (- 0 10877)) (=> _b43 (not _WRITE_HAS_OCCURRED_$$inter$1))))
(=> (=> _b43 (not _WRITE_HAS_OCCURRED_$$inter$1)) (and
(or %lbl%@10885 (=> (= (ControlFlow 0 823) (- 0 10885)) (=> _b44 (=> _WRITE_HAS_OCCURRED_$$inter$1 (= _WRITE_OFFSET_$$inter$1 local_id_x$1)))))
(=> (=> _b44 (=> _WRITE_HAS_OCCURRED_$$inter$1 (= _WRITE_OFFSET_$$inter$1 local_id_x$1))) (and
(or %lbl%@10899 (=> (= (ControlFlow 0 823) (- 0 10899)) (=> _b45 (=> _READ_HAS_OCCURRED_$$inter$1 (= _READ_OFFSET_$$inter$1 local_id_x$1)))))
(=> (=> _b45 (=> _READ_HAS_OCCURRED_$$inter$1 (= _READ_OFFSET_$$inter$1 local_id_x$1))) true))))))))))))))))))))))))))))))))))))))
(let ((PreconditionGeneratedEntry_correct (=> (and %lbl%+9318 true) (=> (bvsgt group_size_x #x00000000) (=> (and
(bvsgt num_groups_x #x00000000)
(bvsge group_id_x$1 #x00000000)
(bvsge group_id_x$2 #x00000000)
(bvslt group_id_x$1 num_groups_x)) (=> (and
(bvslt group_id_x$2 num_groups_x)
(bvsge local_id_x$1 #x00000000)
(bvsge local_id_x$2 #x00000000)
(bvslt local_id_x$1 group_size_x)
(bvslt local_id_x$2 group_size_x)
(bvsgt group_size_y #x00000000)
(bvsgt num_groups_y #x00000000)
(bvsge group_id_y$1 #x00000000)) (=> (and
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
(bvslt local_id_z$1 group_size_z)) (=> (and
(bvslt local_id_z$2 group_size_z)
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (or
(not (= local_id_x$1 local_id_x$2))
(not (= local_id_y$1 local_id_y$2))
(not (= local_id_z$1 local_id_z$2))))
(=> _b0 (= _P$1 _P$2))
(=> _b1 (=> (and
_P$1
_P$2) (= $blockIdx$1 $blockIdx$2)))
(=> _b2 (= $blockIdx$1 $blockIdx$2))
(=> _b3 (=> (and
_P$1
_P$2) (= $blockIdy$1 $blockIdy$2)))
(=> _b4 (= $blockIdy$1 $blockIdy$2))
(=> _b5 (=> (and
_P$1
_P$2) (= $localIdx$1 $localIdx$2)))
(=> _b6 (= $localIdx$1 $localIdx$2))
(=> _b7 (=> (and
_P$1
_P$2) (= $localIdy$1 $localIdy$2)))
(=> _b8 (= $localIdy$1 $localIdy$2))
(=> _b9 (=> (and
_P$1
_P$2) (= $blockWidth$1 $blockWidth$2)))
(=> _b10 (= $blockWidth$1 $blockWidth$2))
(=> _b11 (=> (and
_P$1
_P$2) (= $globalWidth$1 $globalWidth$2)))
(=> _b12 (= $globalWidth$1 $globalWidth$2))
(=> _b13 (not _READ_HAS_OCCURRED_$$output$1))
(=> _b14 (not _WRITE_HAS_OCCURRED_$$output$1))
(=> _b15 (=> _WRITE_HAS_OCCURRED_$$output$1 (= _WRITE_OFFSET_$$output$1 local_id_x$1)))
(=> _b16 (=> _READ_HAS_OCCURRED_$$output$1 (= _READ_OFFSET_$$output$1 local_id_x$1)))
(=> _b17 (not _READ_HAS_OCCURRED_$$input$1))
(=> _b18 (not _WRITE_HAS_OCCURRED_$$input$1))
(=> _b19 (=> _WRITE_HAS_OCCURRED_$$input$1 (= _WRITE_OFFSET_$$input$1 local_id_x$1)))
(=> _b20 (=> _READ_HAS_OCCURRED_$$input$1 (= _READ_OFFSET_$$input$1 local_id_x$1)))
(=> _b21 (not _READ_HAS_OCCURRED_$$dct8x8$1))
(=> _b22 (not _WRITE_HAS_OCCURRED_$$dct8x8$1))
(=> _b23 (=> _WRITE_HAS_OCCURRED_$$dct8x8$1 (= _WRITE_OFFSET_$$dct8x8$1 local_id_x$1)))
(=> _b24 (=> _READ_HAS_OCCURRED_$$dct8x8$1 (= _READ_OFFSET_$$dct8x8$1 local_id_x$1)))
(=> _b25 (not _READ_HAS_OCCURRED_$$inter$1))
(=> _b26 (not _WRITE_HAS_OCCURRED_$$inter$1))
(=> _b27 (=> _WRITE_HAS_OCCURRED_$$inter$1 (= _WRITE_OFFSET_$$inter$1 local_id_x$1)))
(=> _b28 (=> _READ_HAS_OCCURRED_$$inter$1 (= _READ_OFFSET_$$inter$1 local_id_x$1)))
(= (ControlFlow 0 9318) 823)) $entry_correct))))))))
PreconditionGeneratedEntry_correct))))
(declare-fun %lbl%+5094 () Bool)
(declare-fun %lbl%@16466 () Bool)
(declare-fun _P$2@@0 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$output$1@0 () Bool)
(declare-fun _WRITE_OFFSET_$$output$1@0 () (_ BitVec 32))
(declare-fun v2$2@0 () (_ BitVec 32))
(declare-fun %lbl%@16478 () Bool)
(declare-fun %lbl%+5088 () Bool)
(declare-fun _P$1@@0 () Bool)
(declare-fun inline$_LOG_WRITE_$$output$0$track@0 () Bool)
(declare-fun v2$1@0 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$output$1@0 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$output$1 () (_ BitVec 32))
(declare-fun %lbl%+5092 () Bool)
(declare-fun p4$1@3 () Bool)
(declare-fun p4$2@3 () Bool)
(declare-fun %lbl%@16389 () Bool)
(declare-fun %lbl%+5096 () Bool)
(declare-fun %lbl%@16216 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$input$1@1 () Bool)
(declare-fun _READ_SOURCE_$$input$1@1 () (_ BitVec 32))
(declare-fun %lbl%@16224 () Bool)
(declare-fun %lbl%@16230 () Bool)
(declare-fun %lbl%@16240 () Bool)
(declare-fun _WRITE_SOURCE_$$input$1 () (_ BitVec 32))
(declare-fun %lbl%@16252 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$dct8x8$1@3 () Bool)
(declare-fun _READ_SOURCE_$$dct8x8$1@3 () (_ BitVec 32))
(declare-fun %lbl%@16267 () Bool)
(declare-fun %lbl%@16273 () Bool)
(declare-fun %lbl%@16283 () Bool)
(declare-fun _WRITE_SOURCE_$$dct8x8$1 () (_ BitVec 32))
(declare-fun %lbl%@16295 () Bool)
(declare-fun %lbl%@16301 () Bool)
(declare-fun %lbl%@16311 () Bool)
(declare-fun _READ_SOURCE_$$output$1 () (_ BitVec 32))
(declare-fun %lbl%@16323 () Bool)
(declare-fun %lbl%@16335 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$inter$1@1 () Bool)
(declare-fun _READ_SOURCE_$$inter$1@1 () (_ BitVec 32))
(declare-fun %lbl%@16343 () Bool)
(declare-fun _WRITE_HAS_OCCURRED_$$inter$1@0 () Bool)
(declare-fun _WRITE_SOURCE_$$inter$1@0 () (_ BitVec 32))
(declare-fun %lbl%@16351 () Bool)
(declare-fun %lbl%@16361 () Bool)
(declare-fun %lbl%@16371 () Bool)
(declare-fun %lbl%@16376 () Bool)
(declare-fun %lbl%+5010 () Bool)
(declare-fun %lbl%@16114 () Bool)
(declare-fun p5$2@1 () Bool)
(declare-fun $cond37$2@2 () (_ BitVec 32))
(declare-fun $acc.1$1@2 () (_ BitVec 32))
(declare-fun p5$1@1 () Bool)
(declare-fun FADD32 ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
(declare-fun $acc.1$1@1 () (_ BitVec 32))
(declare-fun FMUL32 ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
(declare-fun v11$1@1 () (_ BitVec 32))
(declare-fun v12$1@1 () (_ BitVec 32))
(declare-fun $acc.1$2@2 () (_ BitVec 32))
(declare-fun $acc.1$2@1 () (_ BitVec 32))
(declare-fun v11$2@1 () (_ BitVec 32))
(declare-fun v12$2@1 () (_ BitVec 32))
(declare-fun $k21.0$1@2 () (_ BitVec 32))
(declare-fun $k21.0$1@1 () (_ BitVec 32))
(declare-fun $k21.0$2@2 () (_ BitVec 32))
(declare-fun $k21.0$2@1 () (_ BitVec 32))
(declare-fun p4$1@2 () Bool)
(declare-fun p4$2@2 () Bool)
(declare-fun %lbl%+5004 () Bool)
(declare-fun inline$_LOG_READ_$$dct8x8$1$track@1 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$dct8x8$1@2 () Bool)
(declare-fun _READ_OFFSET_$$dct8x8$1@3 () (_ BitVec 32))
(declare-fun $cond37$1@2 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$dct8x8$1@2 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$dct8x8$1@2 () (_ BitVec 32))
(declare-fun %lbl%+5008 () Bool)
(declare-fun %lbl%@15983 () Bool)
(declare-fun _WRITE_OFFSET_$$inter$1@0 () (_ BitVec 32))
(declare-fun v9$2@1 () (_ BitVec 32))
(declare-fun %lbl%@16019 () Bool)
(declare-fun _HAVOC_bv32$1@5 () (_ BitVec 32))
(declare-fun v12$1@0 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@5 () (_ BitVec 32))
(declare-fun v12$2@0 () (_ BitVec 32))
(declare-fun %lbl%+4922 () Bool)
(declare-fun inline$_LOG_READ_$$inter$0$track@1 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$inter$1@0 () Bool)
(declare-fun _READ_OFFSET_$$inter$1@1 () (_ BitVec 32))
(declare-fun v9$1@1 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$inter$1@0 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$inter$1@0 () (_ BitVec 32))
(declare-fun %lbl%+4926 () Bool)
(declare-fun p4$1@1 () Bool)
(declare-fun p4$2@1 () Bool)
(declare-fun v8$1@1 () Bool)
(declare-fun $blockWidth$1@@0 () (_ BitVec 32))
(declare-fun v8$1@0 () Bool)
(declare-fun v8$2@1 () Bool)
(declare-fun $blockWidth$2@@0 () (_ BitVec 32))
(declare-fun v8$2@0 () Bool)
(declare-fun v0$1@0 () (_ BitVec 32))
(declare-fun v9$1@0 () (_ BitVec 32))
(declare-fun v0$2@0 () (_ BitVec 32))
(declare-fun v9$2@0 () (_ BitVec 32))
(declare-fun v10$1@1 () Bool)
(declare-fun $inverse$1 () (_ BitVec 32))
(declare-fun v10$1@0 () Bool)
(declare-fun v10$2@1 () Bool)
(declare-fun $inverse$2 () (_ BitVec 32))
(declare-fun v10$2@0 () Bool)
(declare-fun p7$1@1 () Bool)
(declare-fun p7$2@1 () Bool)
(declare-fun p6$1@1 () Bool)
(declare-fun p6$2@1 () Bool)
(declare-fun $cond37$1@1 () (_ BitVec 32))
(declare-fun v1$1@0 () (_ BitVec 32))
(declare-fun $cond37$1@0 () (_ BitVec 32))
(declare-fun $cond37$2@1 () (_ BitVec 32))
(declare-fun v1$2@0 () (_ BitVec 32))
(declare-fun $cond37$2@0 () (_ BitVec 32))
(declare-fun %lbl%@15888 () Bool)
(declare-fun _HAVOC_bv32$1@4 () (_ BitVec 32))
(declare-fun v11$1@0 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@4 () (_ BitVec 32))
(declare-fun v11$2@0 () (_ BitVec 32))
(declare-fun %lbl%+4844 () Bool)
(declare-fun $acc.1$1@0 () (_ BitVec 32))
(declare-fun $acc.1$1 () (_ BitVec 32))
(declare-fun $acc.1$2@0 () (_ BitVec 32))
(declare-fun $acc.1$2 () (_ BitVec 32))
(declare-fun $k21.0$1@0 () (_ BitVec 32))
(declare-fun $k21.0$1 () (_ BitVec 32))
(declare-fun $k21.0$2@0 () (_ BitVec 32))
(declare-fun $k21.0$2 () (_ BitVec 32))
(declare-fun p4$1@0 () Bool)
(declare-fun p4$2@0 () Bool)
(declare-fun %lbl%@15146 () Bool)
(declare-fun %lbl%@15154 () Bool)
(declare-fun %lbl%@15160 () Bool)
(declare-fun %lbl%@15170 () Bool)
(declare-fun %lbl%@15182 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$dct8x8$1@1 () Bool)
(declare-fun _READ_SOURCE_$$dct8x8$1@1 () (_ BitVec 32))
(declare-fun %lbl%@15197 () Bool)
(declare-fun %lbl%@15203 () Bool)
(declare-fun %lbl%@15213 () Bool)
(declare-fun %lbl%@15225 () Bool)
(declare-fun %lbl%@15231 () Bool)
(declare-fun %lbl%@15241 () Bool)
(declare-fun %lbl%@15253 () Bool)
(declare-fun %lbl%@15265 () Bool)
(declare-fun _READ_SOURCE_$$inter$1 () (_ BitVec 32))
(declare-fun %lbl%@15275 () Bool)
(declare-fun %lbl%@15283 () Bool)
(declare-fun %lbl%@15295 () Bool)
(declare-fun %lbl%@15305 () Bool)
(declare-fun %lbl%@15310 () Bool)
(declare-fun %lbl%+4840 () Bool)
(declare-fun %lbl%+4828 () Bool)
(declare-fun inline$$bugle_barrier$0$$1$2@0 () (_ BitVec 1))
(declare-fun %lbl%+4830 () Bool)
(declare-fun %lbl%+4826 () Bool)
(declare-fun %lbl%+4824 () Bool)
(declare-fun inline$$bugle_barrier$0$$1$1@0 () (_ BitVec 1))
(declare-fun %lbl%+4832 () Bool)
(declare-fun %lbl%+4822 () Bool)
(declare-fun %lbl%+4820 () Bool)
(declare-fun inline$$bugle_barrier$0$$0$2@0 () (_ BitVec 1))
(declare-fun %lbl%+4834 () Bool)
(declare-fun %lbl%+4818 () Bool)
(declare-fun %lbl%+4816 () Bool)
(declare-fun inline$$bugle_barrier$0$$0$1@0 () (_ BitVec 1))
(declare-fun %lbl%+4836 () Bool)
(declare-fun %lbl%+4814 () Bool)
(declare-fun %lbl%+4838 () Bool)
(declare-fun %lbl%+4810 () Bool)
(declare-fun %lbl%@14709 () Bool)
(declare-fun %lbl%+4842 () Bool)
(declare-fun call1967formal@_offset$2@0 () (_ BitVec 32))
(declare-fun %lbl%@14573 () Bool)
(declare-fun %lbl%@14609 () Bool)
(declare-fun %lbl%+4361 () Bool)
(declare-fun inline$_LOG_WRITE_$$inter$0$track@0 () Bool)
(declare-fun inline$_LOG_WRITE_$$inter$0$_offset$1@0 () (_ BitVec 32))
(declare-fun _WRITE_SOURCE_$$inter$1 () (_ BitVec 32))
(declare-fun %lbl%+4359 () Bool)
(declare-fun %lbl%+4365 () Bool)
(declare-fun p0$1@3 () Bool)
(declare-fun p0$2@3 () Bool)
(declare-fun %lbl%@14472 () Bool)
(declare-fun %lbl%+5098 () Bool)
(declare-fun %lbl%@14291 () Bool)
(declare-fun %lbl%@14299 () Bool)
(declare-fun %lbl%@14305 () Bool)
(declare-fun %lbl%@14315 () Bool)
(declare-fun %lbl%@14327 () Bool)
(declare-fun %lbl%@14342 () Bool)
(declare-fun %lbl%@14348 () Bool)
(declare-fun %lbl%@14358 () Bool)
(declare-fun %lbl%@14370 () Bool)
(declare-fun %lbl%@14376 () Bool)
(declare-fun %lbl%@14386 () Bool)
(declare-fun %lbl%@14398 () Bool)
(declare-fun %lbl%@14410 () Bool)
(declare-fun %lbl%@14420 () Bool)
(declare-fun %lbl%@14430 () Bool)
(declare-fun %lbl%@14442 () Bool)
(declare-fun %lbl%@14454 () Bool)
(declare-fun %lbl%@14459 () Bool)
(declare-fun %lbl%+4283 () Bool)
(declare-fun %lbl%@14189 () Bool)
(declare-fun p1$2@1 () Bool)
(declare-fun call1785formal@$ret$2@0 () (_ BitVec 32))
(declare-fun $acc.0$1@2 () (_ BitVec 32))
(declare-fun p1$1@1 () Bool)
(declare-fun $acc.0$1@1 () (_ BitVec 32))
(declare-fun v6$1@1 () (_ BitVec 32))
(declare-fun v7$1@1 () (_ BitVec 32))
(declare-fun $acc.0$2@2 () (_ BitVec 32))
(declare-fun $acc.0$2@1 () (_ BitVec 32))
(declare-fun v6$2@1 () (_ BitVec 32))
(declare-fun v7$2@1 () (_ BitVec 32))
(declare-fun $k.0$1@2 () (_ BitVec 32))
(declare-fun $k.0$1@1 () (_ BitVec 32))
(declare-fun $k.0$2@2 () (_ BitVec 32))
(declare-fun $k.0$2@1 () (_ BitVec 32))
(declare-fun p0$1@2 () Bool)
(declare-fun p0$2@2 () Bool)
(declare-fun %lbl%+4277 () Bool)
(declare-fun inline$_LOG_READ_$$input$0$track@1 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$input$1@0 () Bool)
(declare-fun _READ_OFFSET_$$input$1@1 () (_ BitVec 32))
(declare-fun call1785formal@$ret$1@0 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$input$1@0 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$input$1@0 () (_ BitVec 32))
(declare-fun %lbl%+4281 () Bool)
(declare-fun %lbl%@14080 () Bool)
(declare-fun $cond$2@2 () (_ BitVec 32))
(declare-fun %lbl%@14094 () Bool)
(declare-fun _HAVOC_bv32$1@2 () (_ BitVec 32))
(declare-fun v7$1@0 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@2 () (_ BitVec 32))
(declare-fun v7$2@0 () (_ BitVec 32))
(declare-fun %lbl%+4195 () Bool)
(declare-fun inline$_LOG_READ_$$dct8x8$0$track@1 () Bool)
(declare-fun _READ_HAS_OCCURRED_$$dct8x8$1@0 () Bool)
(declare-fun _READ_OFFSET_$$dct8x8$1@1 () (_ BitVec 32))
(declare-fun $cond$1@2 () (_ BitVec 32))
(declare-fun _READ_OFFSET_$$dct8x8$1@0 () (_ BitVec 32))
(declare-fun _READ_SOURCE_$$dct8x8$1@0 () (_ BitVec 32))
(declare-fun %lbl%+4199 () Bool)
(declare-fun p0$1@1 () Bool)
(declare-fun p0$2@1 () Bool)
(declare-fun v3$1@1 () Bool)
(declare-fun v3$1@0 () Bool)
(declare-fun v3$2@1 () Bool)
(declare-fun v3$2@0 () Bool)
(declare-fun v4$1@1 () Bool)
(declare-fun v4$1@0 () Bool)
(declare-fun v4$2@1 () Bool)
(declare-fun v4$2@0 () Bool)
(declare-fun p3$1@1 () Bool)
(declare-fun p3$2@1 () Bool)
(declare-fun p2$1@1 () Bool)
(declare-fun p2$2@1 () Bool)
(declare-fun $cond$1@1 () (_ BitVec 32))
(declare-fun $cond$1@0 () (_ BitVec 32))
(declare-fun $cond$2@1 () (_ BitVec 32))
(declare-fun $cond$2@0 () (_ BitVec 32))
(declare-fun %lbl%@13261 () Bool)
(declare-fun %lbl%@13267 () Bool)
(declare-fun %lbl%@13273 () Bool)
(declare-fun %lbl%@13279 () Bool)
(declare-fun %lbl%@13285 () Bool)
(declare-fun %lbl%@13291 () Bool)
(declare-fun %lbl%@13297 () Bool)
(declare-fun %lbl%@13303 () Bool)
(declare-fun %lbl%@13309 () Bool)
(declare-fun %lbl%@13315 () Bool)
(declare-fun %lbl%@13321 () Bool)
(declare-fun %lbl%@13327 () Bool)
(declare-fun %lbl%@13333 () Bool)
(declare-fun %lbl%@13339 () Bool)
(declare-fun %lbl%@13345 () Bool)
(declare-fun %lbl%@13351 () Bool)
(declare-fun %lbl%@13357 () Bool)
(declare-fun %lbl%@13363 () Bool)
(declare-fun %lbl%@13369 () Bool)
(declare-fun %lbl%@13375 () Bool)
(declare-fun %lbl%@13381 () Bool)
(declare-fun %lbl%@13387 () Bool)
(declare-fun %lbl%@13393 () Bool)
(declare-fun %lbl%@13399 () Bool)
(declare-fun %lbl%@13405 () Bool)
(declare-fun %lbl%@13411 () Bool)
(declare-fun %lbl%@13417 () Bool)
(declare-fun %lbl%@13423 () Bool)
(declare-fun %lbl%@13429 () Bool)
(declare-fun %lbl%@13435 () Bool)
(declare-fun %lbl%@13441 () Bool)
(declare-fun %lbl%@13487 () Bool)
(declare-fun %lbl%@13495 () Bool)
(declare-fun %lbl%@13509 () Bool)
(declare-fun %lbl%@13517 () Bool)
(declare-fun %lbl%@13531 () Bool)
(declare-fun %lbl%@13539 () Bool)
(declare-fun %lbl%@13553 () Bool)
(declare-fun %lbl%@13561 () Bool)
(declare-fun %lbl%@13575 () Bool)
(declare-fun %lbl%@13583 () Bool)
(declare-fun %lbl%@13597 () Bool)
(declare-fun %lbl%@13605 () Bool)
(declare-fun $width$1 () (_ BitVec 32))
(declare-fun $width$2 () (_ BitVec 32))
(declare-fun %lbl%@13619 () Bool)
(declare-fun %lbl%@13627 () Bool)
(declare-fun %lbl%@13635 () Bool)
(declare-fun %lbl%@13643 () Bool)
(declare-fun %lbl%@13657 () Bool)
(declare-fun %lbl%@13671 () Bool)
(declare-fun %lbl%@13678 () Bool)
(declare-fun %lbl%@13686 () Bool)
(declare-fun %lbl%@13700 () Bool)
(declare-fun %lbl%@13712 () Bool)
(declare-fun %lbl%@13719 () Bool)
(declare-fun %lbl%@13727 () Bool)
(declare-fun %lbl%@13741 () Bool)
(declare-fun %lbl%@13753 () Bool)
(declare-fun %lbl%@13761 () Bool)
(declare-fun %lbl%@13769 () Bool)
(declare-fun %lbl%@13783 () Bool)
(declare-fun %lbl%@13985 () Bool)
(declare-fun _HAVOC_bv32$1@1 () (_ BitVec 32))
(declare-fun v6$1@0 () (_ BitVec 32))
(declare-fun _HAVOC_bv32$2@1 () (_ BitVec 32))
(declare-fun v6$2@0 () (_ BitVec 32))
(declare-fun %lbl%+4117 () Bool)
(declare-fun v0$1 () (_ BitVec 32))
(declare-fun v0$2 () (_ BitVec 32))
(declare-fun v1$1 () (_ BitVec 32))
(declare-fun v1$2 () (_ BitVec 32))
(declare-fun v2$1 () (_ BitVec 32))
(declare-fun v2$2 () (_ BitVec 32))
(declare-fun $acc.0$1@0 () (_ BitVec 32))
(declare-fun $acc.0$1 () (_ BitVec 32))
(declare-fun $acc.0$2@0 () (_ BitVec 32))
(declare-fun $acc.0$2 () (_ BitVec 32))
(declare-fun $k.0$1@0 () (_ BitVec 32))
(declare-fun $k.0$1 () (_ BitVec 32))
(declare-fun $k.0$2@0 () (_ BitVec 32))
(declare-fun $k.0$2 () (_ BitVec 32))
(declare-fun p0$1@0 () Bool)
(declare-fun p0$2@0 () Bool)
(declare-fun %lbl%@12497 () Bool)
(declare-fun _READ_SOURCE_$$input$1 () (_ BitVec 32))
(declare-fun %lbl%@12507 () Bool)
(declare-fun %lbl%@12513 () Bool)
(declare-fun %lbl%@12525 () Bool)
(declare-fun %lbl%@12537 () Bool)
(declare-fun _READ_SOURCE_$$dct8x8$1 () (_ BitVec 32))
(declare-fun %lbl%@12555 () Bool)
(declare-fun %lbl%@12561 () Bool)
(declare-fun %lbl%@12573 () Bool)
(declare-fun %lbl%@12585 () Bool)
(declare-fun %lbl%@12591 () Bool)
(declare-fun %lbl%@12601 () Bool)
(declare-fun %lbl%@12613 () Bool)
(declare-fun %lbl%@12625 () Bool)
(declare-fun %lbl%@12635 () Bool)
(declare-fun %lbl%@12645 () Bool)
(declare-fun %lbl%@12657 () Bool)
(declare-fun %lbl%@12669 () Bool)
(declare-fun %lbl%@12674 () Bool)
(declare-fun %lbl%+11167 () Bool)
(define-fun $DCT () Bool (=> (= (ControlFlow 0 0) 11167) (let (($for.cond22.tail$1_correct (=> (and %lbl%+5094 true) (and
(or %lbl%@16466 (=> (= (ControlFlow 0 5094) (- 0 16466)) (not (and
_P$2@@0
_WRITE_HAS_OCCURRED_$$output$1@0
(= _WRITE_OFFSET_$$output$1@0 v2$2@0)))))
(=> (not (and
_P$2@@0
_WRITE_HAS_OCCURRED_$$output$1@0
(= _WRITE_OFFSET_$$output$1@0 v2$2@0))) (and
(or %lbl%@16478 (=> (= (ControlFlow 0 5094) (- 0 16478)) (not (and
_P$2@@0
_READ_HAS_OCCURRED_$$output$1
(= _READ_OFFSET_$$output$1 v2$2@0)))))
(=> (not (and
_P$2@@0
_READ_HAS_OCCURRED_$$output$1
(= _READ_OFFSET_$$output$1 v2$2@0))) true)))))))
(let ((inline$_LOG_WRITE_$$output$0$_LOG_WRITE_correct (=> (and %lbl%+5088 true) (=> (and
(= _WRITE_HAS_OCCURRED_$$output$1@0 (ite (and
_P$1@@0
inline$_LOG_WRITE_$$output$0$track@0) true _WRITE_HAS_OCCURRED_$$output$1))
(= _WRITE_OFFSET_$$output$1@0 (ite (and
_P$1@@0
inline$_LOG_WRITE_$$output$0$track@0) v2$1@0 _WRITE_OFFSET_$$output$1))
(= _WRITE_SOURCE_$$output$1@0 (ite (and
_P$1@@0
inline$_LOG_WRITE_$$output$0$track@0) #x00000002 _WRITE_SOURCE_$$output$1))
(= (ControlFlow 0 5088) 5094)) $for.cond22.tail$1_correct))))
(let (($for.cond22.tail_correct (=> (and %lbl%+5092 true) (=> (and
(not p4$1@3)
(not p4$2@3)) (and
(or %lbl%@16389 (=> (= (ControlFlow 0 5092) (- 0 16389)) (=> _P$1@@0 true)))
(=> (=> _P$1@@0 true) (=> (= (ControlFlow 0 5092) 5088) inline$_LOG_WRITE_$$output$0$_LOG_WRITE_correct)))))))
(let (($for.cond22.backedge_correct (=> (and %lbl%+5096 true) (=> (or
p4$1@3
p4$2@3) (and
(or %lbl%@16216 (=> (= (ControlFlow 0 5096) (- 0 16216)) (=> _READ_HAS_OCCURRED_$$input$1@1 (= _READ_SOURCE_$$input$1@1 #x00000006))))
(=> (=> _READ_HAS_OCCURRED_$$input$1@1 (= _READ_SOURCE_$$input$1@1 #x00000006)) (and
(or %lbl%@16224 (=> (= (ControlFlow 0 5096) (- 0 16224)) (=> _WRITE_HAS_OCCURRED_$$input$1 false)))
(=> (=> _WRITE_HAS_OCCURRED_$$input$1 false) (and
(or %lbl%@16230 (=> (= (ControlFlow 0 5096) (- 0 16230)) (=> (not _READ_HAS_OCCURRED_$$input$1@1) (= _READ_SOURCE_$$input$1@1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$input$1@1) (= _READ_SOURCE_$$input$1@1 #x00000000)) (and
(or %lbl%@16240 (=> (= (ControlFlow 0 5096) (- 0 16240)) (=> (not _WRITE_HAS_OCCURRED_$$input$1) (= _WRITE_SOURCE_$$input$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$input$1) (= _WRITE_SOURCE_$$input$1 #x00000000)) (and
(or %lbl%@16252 (=> (= (ControlFlow 0 5096) (- 0 16252)) (=> _READ_HAS_OCCURRED_$$dct8x8$1@3 (or
(= _READ_SOURCE_$$dct8x8$1@3 #x00000004)
(= _READ_SOURCE_$$dct8x8$1@3 #x00000005)))))
(=> (=> _READ_HAS_OCCURRED_$$dct8x8$1@3 (or
(= _READ_SOURCE_$$dct8x8$1@3 #x00000004)
(= _READ_SOURCE_$$dct8x8$1@3 #x00000005))) (and
(or %lbl%@16267 (=> (= (ControlFlow 0 5096) (- 0 16267)) (=> _WRITE_HAS_OCCURRED_$$dct8x8$1 false)))
(=> (=> _WRITE_HAS_OCCURRED_$$dct8x8$1 false) (and
(or %lbl%@16273 (=> (= (ControlFlow 0 5096) (- 0 16273)) (=> (not _READ_HAS_OCCURRED_$$dct8x8$1@3) (= _READ_SOURCE_$$dct8x8$1@3 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$dct8x8$1@3) (= _READ_SOURCE_$$dct8x8$1@3 #x00000000)) (and
(or %lbl%@16283 (=> (= (ControlFlow 0 5096) (- 0 16283)) (=> (not _WRITE_HAS_OCCURRED_$$dct8x8$1) (= _WRITE_SOURCE_$$dct8x8$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$dct8x8$1) (= _WRITE_SOURCE_$$dct8x8$1 #x00000000)) (and
(or %lbl%@16295 (=> (= (ControlFlow 0 5096) (- 0 16295)) (=> _READ_HAS_OCCURRED_$$output$1 false)))
(=> (=> _READ_HAS_OCCURRED_$$output$1 false) (and
(or %lbl%@16301 (=> (= (ControlFlow 0 5096) (- 0 16301)) (=> _WRITE_HAS_OCCURRED_$$output$1 (= _WRITE_SOURCE_$$output$1 #x00000002))))
(=> (=> _WRITE_HAS_OCCURRED_$$output$1 (= _WRITE_SOURCE_$$output$1 #x00000002)) (and
(or %lbl%@16311 (=> (= (ControlFlow 0 5096) (- 0 16311)) (=> (not _READ_HAS_OCCURRED_$$output$1) (= _READ_SOURCE_$$output$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$output$1) (= _READ_SOURCE_$$output$1 #x00000000)) (and
(or %lbl%@16323 (=> (= (ControlFlow 0 5096) (- 0 16323)) (=> (not _WRITE_HAS_OCCURRED_$$output$1) (= _WRITE_SOURCE_$$output$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$output$1) (= _WRITE_SOURCE_$$output$1 #x00000000)) (and
(or %lbl%@16335 (=> (= (ControlFlow 0 5096) (- 0 16335)) (=> _READ_HAS_OCCURRED_$$inter$1@1 (= _READ_SOURCE_$$inter$1@1 #x00000003))))
(=> (=> _READ_HAS_OCCURRED_$$inter$1@1 (= _READ_SOURCE_$$inter$1@1 #x00000003)) (and
(or %lbl%@16343 (=> (= (ControlFlow 0 5096) (- 0 16343)) (=> _WRITE_HAS_OCCURRED_$$inter$1@0 (= _WRITE_SOURCE_$$inter$1@0 #x00000001))))
(=> (=> _WRITE_HAS_OCCURRED_$$inter$1@0 (= _WRITE_SOURCE_$$inter$1@0 #x00000001)) (and
(or %lbl%@16351 (=> (= (ControlFlow 0 5096) (- 0 16351)) (=> (not _READ_HAS_OCCURRED_$$inter$1@1) (= _READ_SOURCE_$$inter$1@1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$inter$1@1) (= _READ_SOURCE_$$inter$1@1 #x00000000)) (and
(or %lbl%@16361 (=> (= (ControlFlow 0 5096) (- 0 16361)) (=> (not _WRITE_HAS_OCCURRED_$$inter$1@0) (= _WRITE_SOURCE_$$inter$1@0 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$inter$1@0) (= _WRITE_SOURCE_$$inter$1@0 #x00000000)) (and
(or %lbl%@16371 (=> (= (ControlFlow 0 5096) (- 0 16371)) (=> p4$1@3 _P$1@@0)))
(=> (=> p4$1@3 _P$1@@0) (and
(or %lbl%@16376 (=> (= (ControlFlow 0 5096) (- 0 16376)) (=> p4$2@3 _P$2@@0)))
(=> (=> p4$2@3 _P$2@@0) true))))))))))))))))))))))))))))))))))))))))
(let (($for.cond22$2_correct (=> (and %lbl%+5010 true) (and
(or %lbl%@16114 (=> (= (ControlFlow 0 5010) (- 0 16114)) (not (and
p5$2@1
_WRITE_HAS_OCCURRED_$$dct8x8$1
(= _WRITE_OFFSET_$$dct8x8$1 $cond37$2@2)))))
(=> (not (and
p5$2@1
_WRITE_HAS_OCCURRED_$$dct8x8$1
(= _WRITE_OFFSET_$$dct8x8$1 $cond37$2@2))) (=> (and
(= $acc.1$1@2 (ite p5$1@1 (FADD32 $acc.1$1@1 (FMUL32 v11$1@1 v12$1@1)) $acc.1$1@1))
(= $acc.1$2@2 (ite p5$2@1 (FADD32 $acc.1$2@1 (FMUL32 v11$2@1 v12$2@1)) $acc.1$2@1))
(= $k21.0$1@2 (ite p5$1@1 (bvadd $k21.0$1@1 #x00000001) $k21.0$1@1))
(= $k21.0$2@2 (ite p5$2@1 (bvadd $k21.0$2@1 #x00000001) $k21.0$2@1))
(= p4$1@3 (ite p5$1@1 true p4$1@2))
(= p4$2@3 (ite p5$2@1 true p4$2@2))) (and
(=> (= (ControlFlow 0 5010) 5096) $for.cond22.backedge_correct)
(=> (= (ControlFlow 0 5010) 5092) $for.cond22.tail_correct))))))))
(let ((inline$_LOG_READ_$$dct8x8$1$_LOG_READ_correct (=> (and %lbl%+5004 true) (=> (and
(= _READ_HAS_OCCURRED_$$dct8x8$1@3 (ite (and
p5$1@1
inline$_LOG_READ_$$dct8x8$1$track@1) true _READ_HAS_OCCURRED_$$dct8x8$1@2))
(= _READ_OFFSET_$$dct8x8$1@3 (ite (and
p5$1@1
inline$_LOG_READ_$$dct8x8$1$track@1) $cond37$1@2 _READ_OFFSET_$$dct8x8$1@2))
(= _READ_SOURCE_$$dct8x8$1@3 (ite (and
p5$1@1
inline$_LOG_READ_$$dct8x8$1$track@1) #x00000004 _READ_SOURCE_$$dct8x8$1@2))
(= (ControlFlow 0 5004) 5010)) $for.cond22$2_correct))))
(let (($for.cond22$1_correct (=> (and %lbl%+5008 true) (and
(or %lbl%@15983 (=> (= (ControlFlow 0 5008) (- 0 15983)) (not (and
p5$2@1
_WRITE_HAS_OCCURRED_$$inter$1@0
(= _WRITE_OFFSET_$$inter$1@0 v9$2@1)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)))))
(=> (not (and
p5$2@1
_WRITE_HAS_OCCURRED_$$inter$1@0
(= _WRITE_OFFSET_$$inter$1@0 v9$2@1)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2))) (and
(or %lbl%@16019 (=> (= (ControlFlow 0 5008) (- 0 16019)) (=> p5$1@1 true)))
(=> (=> p5$1@1 true) (=> (and
(= v12$1@1 (ite p5$1@1 _HAVOC_bv32$1@5 v12$1@0))
(= v12$2@1 (ite p5$2@1 _HAVOC_bv32$2@5 v12$2@0))
(= (ControlFlow 0 5008) 5004)) inline$_LOG_READ_$$dct8x8$1$_LOG_READ_correct))))))))
(let ((inline$_LOG_READ_$$inter$0$_LOG_READ_correct (=> (and %lbl%+4922 true) (=> (and
(= _READ_HAS_OCCURRED_$$inter$1@1 (ite (and
p5$1@1
inline$_LOG_READ_$$inter$0$track@1) true _READ_HAS_OCCURRED_$$inter$1@0))
(= _READ_OFFSET_$$inter$1@1 (ite (and
p5$1@1
inline$_LOG_READ_$$inter$0$track@1) v9$1@1 _READ_OFFSET_$$inter$1@0))
(= _READ_SOURCE_$$inter$1@1 (ite (and
p5$1@1
inline$_LOG_READ_$$inter$0$track@1) #x00000003 _READ_SOURCE_$$inter$1@0))
(= (ControlFlow 0 4922) 5008)) $for.cond22$1_correct))))
(let (($for.cond22_correct (=> (and %lbl%+4926 true) (=> (and
(=> _READ_HAS_OCCURRED_$$input$1@1 (= _READ_SOURCE_$$input$1@1 #x00000006))
(=> _WRITE_HAS_OCCURRED_$$input$1 false)
(=> (not _READ_HAS_OCCURRED_$$input$1@1) (= _READ_SOURCE_$$input$1@1 #x00000000))
(=> (not _WRITE_HAS_OCCURRED_$$input$1) (= _WRITE_SOURCE_$$input$1 #x00000000))) (=> (and
(=> _READ_HAS_OCCURRED_$$dct8x8$1@2 (or
(= _READ_SOURCE_$$dct8x8$1@2 #x00000004)
(= _READ_SOURCE_$$dct8x8$1@2 #x00000005)))
(=> _WRITE_HAS_OCCURRED_$$dct8x8$1 false)
(=> (not _READ_HAS_OCCURRED_$$dct8x8$1@2) (= _READ_SOURCE_$$dct8x8$1@2 #x00000000))
(=> (not _WRITE_HAS_OCCURRED_$$dct8x8$1) (= _WRITE_SOURCE_$$dct8x8$1 #x00000000))
(=> _READ_HAS_OCCURRED_$$output$1 false)
(=> _WRITE_HAS_OCCURRED_$$output$1 (= _WRITE_SOURCE_$$output$1 #x00000002))
(=> (not _READ_HAS_OCCURRED_$$output$1) (= _READ_SOURCE_$$output$1 #x00000000))
(=> (not _WRITE_HAS_OCCURRED_$$output$1) (= _WRITE_SOURCE_$$output$1 #x00000000))
(=> _READ_HAS_OCCURRED_$$inter$1@0 (= _READ_SOURCE_$$inter$1@0 #x00000003))
(=> _WRITE_HAS_OCCURRED_$$inter$1@0 (= _WRITE_SOURCE_$$inter$1@0 #x00000001))
(=> (not _READ_HAS_OCCURRED_$$inter$1@0) (= _READ_SOURCE_$$inter$1@0 #x00000000))
(=> (not _WRITE_HAS_OCCURRED_$$inter$1@0) (= _WRITE_SOURCE_$$inter$1@0 #x00000000))
(=> p4$1@1 _P$1@@0)
(=> p4$2@1 _P$2@@0)
(= v8$1@1 (ite p4$1@1 (bvult $k21.0$1@1 $blockWidth$1@@0) v8$1@0))
(= v8$2@1 (ite p4$2@1 (bvult $k21.0$2@1 $blockWidth$2@@0) v8$2@0))
(= p5$1@1 (ite p4$1@1 v8$1@1 false))
(= p5$2@1 (ite p4$2@1 v8$2@1 false))
(= p4$1@2 (ite p4$1@1 v8$1@1 p4$1@1))
(= p4$2@2 (ite p4$2@1 v8$2@1 p4$2@1))
(= v9$1@1 (ite p5$1@1 (bvadd (bvmul v0$1@0 $blockWidth$1@@0) $k21.0$1@1) v9$1@0))
(= v9$2@1 (ite p5$2@1 (bvadd (bvmul v0$2@0 $blockWidth$2@@0) $k21.0$2@1) v9$2@0))
(= v10$1@1 (ite p5$1@1 (not (= $inverse$1 #x00000000)) v10$1@0))
(= v10$2@1 (ite p5$2@1 (not (= $inverse$2 #x00000000)) v10$2@0))
(= p7$1@1 (ite p5$1@1 v10$1@1 false))
(= p7$2@1 (ite p5$2@1 v10$2@1 false))
(= p6$1@1 (ite p5$1@1 (not v10$1@1) false))
(= p6$2@1 (ite p5$2@1 (not v10$2@1) false))
(= $cond37$1@1 (ite p6$1@1 (bvadd (bvmul $k21.0$1@1 $blockWidth$1@@0) v1$1@0) $cond37$1@0))
(= $cond37$2@1 (ite p6$2@1 (bvadd (bvmul $k21.0$2@1 $blockWidth$2@@0) v1$2@0) $cond37$2@0))
(= $cond37$1@2 (ite p7$1@1 (bvadd (bvmul v1$1@0 $blockWidth$1@@0) $k21.0$1@1) $cond37$1@1))
(= $cond37$2@2 (ite p7$2@1 (bvadd (bvmul v1$2@0 $blockWidth$2@@0) $k21.0$2@1) $cond37$2@1))) (and
(or %lbl%@15888 (=> (= (ControlFlow 0 4926) (- 0 15888)) (=> p5$1@1 true)))
(=> (=> p5$1@1 true) (=> (and
(= v11$1@1 (ite p5$1@1 _HAVOC_bv32$1@4 v11$1@0))
(= v11$2@1 (ite p5$2@1 _HAVOC_bv32$2@4 v11$2@0))
(= (ControlFlow 0 4926) 4922)) inline$_LOG_READ_$$inter$0$_LOG_READ_correct))))))))
(let (($for.cond.tail$2_correct (=> (and %lbl%+4844 true) (=> (and
(= $acc.1$1@0 (ite _P$1@@0 #x00000000 $acc.1$1))
(= $acc.1$2@0 (ite _P$2@@0 #x00000000 $acc.1$2))
(= $k21.0$1@0 (ite _P$1@@0 #x00000000 $k21.0$1))
(= $k21.0$2@0 (ite _P$2@@0 #x00000000 $k21.0$2))
(= p4$1@0 (ite _P$1@@0 true false))
(= p4$2@0 (ite _P$2@@0 true false))) (and
(or %lbl%@15146 (=> (= (ControlFlow 0 4844) (- 0 15146)) (=> _READ_HAS_OCCURRED_$$input$1@1 (= _READ_SOURCE_$$input$1@1 #x00000006))))
(=> (=> _READ_HAS_OCCURRED_$$input$1@1 (= _READ_SOURCE_$$input$1@1 #x00000006)) (and
(or %lbl%@15154 (=> (= (ControlFlow 0 4844) (- 0 15154)) (=> _WRITE_HAS_OCCURRED_$$input$1 false)))
(=> (=> _WRITE_HAS_OCCURRED_$$input$1 false) (and
(or %lbl%@15160 (=> (= (ControlFlow 0 4844) (- 0 15160)) (=> (not _READ_HAS_OCCURRED_$$input$1@1) (= _READ_SOURCE_$$input$1@1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$input$1@1) (= _READ_SOURCE_$$input$1@1 #x00000000)) (and
(or %lbl%@15170 (=> (= (ControlFlow 0 4844) (- 0 15170)) (=> (not _WRITE_HAS_OCCURRED_$$input$1) (= _WRITE_SOURCE_$$input$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$input$1) (= _WRITE_SOURCE_$$input$1 #x00000000)) (and
(or %lbl%@15182 (=> (= (ControlFlow 0 4844) (- 0 15182)) (=> _READ_HAS_OCCURRED_$$dct8x8$1@1 (or
(= _READ_SOURCE_$$dct8x8$1@1 #x00000004)
(= _READ_SOURCE_$$dct8x8$1@1 #x00000005)))))
(=> (=> _READ_HAS_OCCURRED_$$dct8x8$1@1 (or
(= _READ_SOURCE_$$dct8x8$1@1 #x00000004)
(= _READ_SOURCE_$$dct8x8$1@1 #x00000005))) (and
(or %lbl%@15197 (=> (= (ControlFlow 0 4844) (- 0 15197)) (=> _WRITE_HAS_OCCURRED_$$dct8x8$1 false)))
(=> (=> _WRITE_HAS_OCCURRED_$$dct8x8$1 false) (and
(or %lbl%@15203 (=> (= (ControlFlow 0 4844) (- 0 15203)) (=> (not _READ_HAS_OCCURRED_$$dct8x8$1@1) (= _READ_SOURCE_$$dct8x8$1@1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$dct8x8$1@1) (= _READ_SOURCE_$$dct8x8$1@1 #x00000000)) (and
(or %lbl%@15213 (=> (= (ControlFlow 0 4844) (- 0 15213)) (=> (not _WRITE_HAS_OCCURRED_$$dct8x8$1) (= _WRITE_SOURCE_$$dct8x8$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$dct8x8$1) (= _WRITE_SOURCE_$$dct8x8$1 #x00000000)) (and
(or %lbl%@15225 (=> (= (ControlFlow 0 4844) (- 0 15225)) (=> _READ_HAS_OCCURRED_$$output$1 false)))
(=> (=> _READ_HAS_OCCURRED_$$output$1 false) (and
(or %lbl%@15231 (=> (= (ControlFlow 0 4844) (- 0 15231)) (=> _WRITE_HAS_OCCURRED_$$output$1 (= _WRITE_SOURCE_$$output$1 #x00000002))))
(=> (=> _WRITE_HAS_OCCURRED_$$output$1 (= _WRITE_SOURCE_$$output$1 #x00000002)) (and
(or %lbl%@15241 (=> (= (ControlFlow 0 4844) (- 0 15241)) (=> (not _READ_HAS_OCCURRED_$$output$1) (= _READ_SOURCE_$$output$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$output$1) (= _READ_SOURCE_$$output$1 #x00000000)) (and
(or %lbl%@15253 (=> (= (ControlFlow 0 4844) (- 0 15253)) (=> (not _WRITE_HAS_OCCURRED_$$output$1) (= _WRITE_SOURCE_$$output$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$output$1) (= _WRITE_SOURCE_$$output$1 #x00000000)) (and
(or %lbl%@15265 (=> (= (ControlFlow 0 4844) (- 0 15265)) (=> _READ_HAS_OCCURRED_$$inter$1 (= _READ_SOURCE_$$inter$1 #x00000003))))
(=> (=> _READ_HAS_OCCURRED_$$inter$1 (= _READ_SOURCE_$$inter$1 #x00000003)) (and
(or %lbl%@15275 (=> (= (ControlFlow 0 4844) (- 0 15275)) (=> _WRITE_HAS_OCCURRED_$$inter$1@0 (= _WRITE_SOURCE_$$inter$1@0 #x00000001))))
(=> (=> _WRITE_HAS_OCCURRED_$$inter$1@0 (= _WRITE_SOURCE_$$inter$1@0 #x00000001)) (and
(or %lbl%@15283 (=> (= (ControlFlow 0 4844) (- 0 15283)) (=> (not _READ_HAS_OCCURRED_$$inter$1) (= _READ_SOURCE_$$inter$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$inter$1) (= _READ_SOURCE_$$inter$1 #x00000000)) (and
(or %lbl%@15295 (=> (= (ControlFlow 0 4844) (- 0 15295)) (=> (not _WRITE_HAS_OCCURRED_$$inter$1@0) (= _WRITE_SOURCE_$$inter$1@0 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$inter$1@0) (= _WRITE_SOURCE_$$inter$1@0 #x00000000)) (and
(or %lbl%@15305 (=> (= (ControlFlow 0 4844) (- 0 15305)) (=> p4$1@0 _P$1@@0)))
(=> (=> p4$1@0 _P$1@@0) (and
(or %lbl%@15310 (=> (= (ControlFlow 0 4844) (- 0 15310)) (=> p4$2@0 _P$2@@0)))
(=> (=> p4$2@0 _P$2@@0) (=> (= (ControlFlow 0 4844) 4926) $for.cond22_correct)))))))))))))))))))))))))))))))))))))))))
(let ((inline$$bugle_barrier$0$Return_correct (=> (and %lbl%+4840 true) (=> (= (ControlFlow 0 4840) 4844) $for.cond.tail$2_correct))))
(let ((inline$$bugle_barrier$0$anon16_Else_correct (=> (and %lbl%+4828 true) (=> (and
(not (and
_P$2@@0
(= inline$$bugle_barrier$0$$1$2@0 #b1)))
(= (ControlFlow 0 4828) 4840)) inline$$bugle_barrier$0$Return_correct))))
(let ((inline$$bugle_barrier$0$anon16_Then_correct (=> (and %lbl%+4830 true) (=> (and
_P$2@@0
(= inline$$bugle_barrier$0$$1$2@0 #b1)
(= (ControlFlow 0 4830) 4840)) inline$$bugle_barrier$0$Return_correct))))
(let ((inline$$bugle_barrier$0$anon8_correct (=> (and %lbl%+4826 true) (and
(=> (= (ControlFlow 0 4826) 4830) inline$$bugle_barrier$0$anon16_Then_correct)
(=> (= (ControlFlow 0 4826) 4828) inline$$bugle_barrier$0$anon16_Else_correct)))))
(let ((inline$$bugle_barrier$0$anon15_Else_correct (=> (and %lbl%+4824 true) (=> (and
(not (and
_P$1@@0
(= inline$$bugle_barrier$0$$1$1@0 #b1)))
(= (ControlFlow 0 4824) 4826)) inline$$bugle_barrier$0$anon8_correct))))
(let ((inline$$bugle_barrier$0$anon15_Then_correct (=> (and %lbl%+4832 true) (=> (and
_P$1@@0
(= inline$$bugle_barrier$0$$1$1@0 #b1)
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _READ_HAS_OCCURRED_$$output$1))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _WRITE_HAS_OCCURRED_$$output$1))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _READ_HAS_OCCURRED_$$input$1@1))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _WRITE_HAS_OCCURRED_$$input$1))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _READ_HAS_OCCURRED_$$dct8x8$1@1))
(=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (not _WRITE_HAS_OCCURRED_$$dct8x8$1))) (and
(=> (= (ControlFlow 0 4832) 4830) inline$$bugle_barrier$0$anon16_Then_correct)
(=> (= (ControlFlow 0 4832) 4828) inline$$bugle_barrier$0$anon16_Else_correct))))))
(let ((inline$$bugle_barrier$0$anon4_correct (=> (and %lbl%+4822 true) (and
(=> (= (ControlFlow 0 4822) 4832) inline$$bugle_barrier$0$anon15_Then_correct)
(=> (= (ControlFlow 0 4822) 4824) inline$$bugle_barrier$0$anon15_Else_correct)))))
(let ((inline$$bugle_barrier$0$anon14_Else_correct (=> (and %lbl%+4820 true) (=> (and
(not (and
_P$2@@0
(= inline$$bugle_barrier$0$$0$2@0 #b1)))
(= (ControlFlow 0 4820) 4822)) inline$$bugle_barrier$0$anon4_correct))))
(let ((inline$$bugle_barrier$0$anon14_Then_correct (=> (and %lbl%+4834 true) (=> (and
_P$2@@0
(= inline$$bugle_barrier$0$$0$2@0 #b1)) (and
(=> (= (ControlFlow 0 4834) 4832) inline$$bugle_barrier$0$anon15_Then_correct)
(=> (= (ControlFlow 0 4834) 4824) inline$$bugle_barrier$0$anon15_Else_correct))))))
(let ((inline$$bugle_barrier$0$anon2_correct (=> (and %lbl%+4818 true) (and
(=> (= (ControlFlow 0 4818) 4834) inline$$bugle_barrier$0$anon14_Then_correct)
(=> (= (ControlFlow 0 4818) 4820) inline$$bugle_barrier$0$anon14_Else_correct)))))
(let ((inline$$bugle_barrier$0$anon13_Else_correct (=> (and %lbl%+4816 true) (=> (and
(not (and
_P$1@@0
(= inline$$bugle_barrier$0$$0$1@0 #b1)))
(= (ControlFlow 0 4816) 4818)) inline$$bugle_barrier$0$anon2_correct))))
(let ((inline$$bugle_barrier$0$anon13_Then_correct (=> (and %lbl%+4836 true) (=> (and
_P$1@@0
(= inline$$bugle_barrier$0$$0$1@0 #b1)
(not _READ_HAS_OCCURRED_$$inter$1)
(not _WRITE_HAS_OCCURRED_$$inter$1@0)) (and
(=> (= (ControlFlow 0 4836) 4834) inline$$bugle_barrier$0$anon14_Then_correct)
(=> (= (ControlFlow 0 4836) 4820) inline$$bugle_barrier$0$anon14_Else_correct))))))
(let ((inline$$bugle_barrier$0$anon12_Else_correct (=> (and %lbl%+4814 true) (=> (not (or
(and
(not _P$1@@0)
(not _P$2@@0))
(and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)
(or
(not _P$1@@0)
(not _P$2@@0))))) (and
(=> (= (ControlFlow 0 4814) 4836) inline$$bugle_barrier$0$anon13_Then_correct)
(=> (= (ControlFlow 0 4814) 4816) inline$$bugle_barrier$0$anon13_Else_correct))))))
(let ((inline$$bugle_barrier$0$anon12_Then_correct (=> (and %lbl%+4838 true) (=> (and
(or
(and
(not _P$1@@0)
(not _P$2@@0))
(and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)
(or
(not _P$1@@0)
(not _P$2@@0))))
(= (ControlFlow 0 4838) 4844)) $for.cond.tail$2_correct))))
(let ((inline$$bugle_barrier$0$Entry_correct (=> (and %lbl%+4810 true) (=> (and
(= inline$$bugle_barrier$0$$0$1@0 (ite true #b1 #b0))
(= inline$$bugle_barrier$0$$1$1@0 (ite false #b1 #b0))
(= inline$$bugle_barrier$0$$0$2@0 (ite true #b1 #b0))
(= inline$$bugle_barrier$0$$1$2@0 (ite false #b1 #b0))) (and
(or %lbl%@14709 (=> (= (ControlFlow 0 4810) (- 0 14709)) (=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (= _P$1@@0 _P$2@@0))))
(=> (=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (= _P$1@@0 _P$2@@0)) (and
(=> (= (ControlFlow 0 4810) 4838) inline$$bugle_barrier$0$anon12_Then_correct)
(=> (= (ControlFlow 0 4810) 4814) inline$$bugle_barrier$0$anon12_Else_correct))))))))
(let (($for.cond.tail$1_correct (=> (and %lbl%+4842 true) (=> (= call1967formal@_offset$2@0 (bvadd (bvmul v1$2@0 $blockWidth$2@@0) v0$2@0)) (and
(or %lbl%@14573 (=> (= (ControlFlow 0 4842) (- 0 14573)) (not (and
_P$2@@0
_WRITE_HAS_OCCURRED_$$inter$1@0
(= _WRITE_OFFSET_$$inter$1@0 call1967formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)))))
(=> (not (and
_P$2@@0
_WRITE_HAS_OCCURRED_$$inter$1@0
(= _WRITE_OFFSET_$$inter$1@0 call1967formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2))) (and
(or %lbl%@14609 (=> (= (ControlFlow 0 4842) (- 0 14609)) (not (and
_P$2@@0
_READ_HAS_OCCURRED_$$inter$1
(= _READ_OFFSET_$$inter$1 call1967formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)))))
(=> (not (and
_P$2@@0
_READ_HAS_OCCURRED_$$inter$1
(= _READ_OFFSET_$$inter$1 call1967formal@_offset$2@0)
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2))) (=> (= (ControlFlow 0 4842) 4810) inline$$bugle_barrier$0$Entry_correct)))))))))
(let ((inline$_LOG_WRITE_$$inter$0$_LOG_WRITE_correct (=> (and %lbl%+4361 true) (=> (and
(= _WRITE_HAS_OCCURRED_$$inter$1@0 (ite (and
_P$1@@0
inline$_LOG_WRITE_$$inter$0$track@0) true _WRITE_HAS_OCCURRED_$$inter$1))
(= _WRITE_OFFSET_$$inter$1@0 (ite (and
_P$1@@0
inline$_LOG_WRITE_$$inter$0$track@0) inline$_LOG_WRITE_$$inter$0$_offset$1@0 _WRITE_OFFSET_$$inter$1))
(= _WRITE_SOURCE_$$inter$1@0 (ite (and
_P$1@@0
inline$_LOG_WRITE_$$inter$0$track@0) #x00000001 _WRITE_SOURCE_$$inter$1))
(= (ControlFlow 0 4361) 4842)) $for.cond.tail$1_correct))))
(let ((inline$_LOG_WRITE_$$inter$0$Entry_correct (=> (and %lbl%+4359 true) (=> (and
(= inline$_LOG_WRITE_$$inter$0$_offset$1@0 (bvadd (bvmul v1$1@0 $blockWidth$1@@0) v0$1@0))
(= (ControlFlow 0 4359) 4361)) inline$_LOG_WRITE_$$inter$0$_LOG_WRITE_correct))))
(let (($for.cond.tail_correct (=> (and %lbl%+4365 true) (=> (and
(not p0$1@3)
(not p0$2@3)) (and
(or %lbl%@14472 (=> (= (ControlFlow 0 4365) (- 0 14472)) (=> _P$1@@0 true)))
(=> (=> _P$1@@0 true) (=> (= (ControlFlow 0 4365) 4359) inline$_LOG_WRITE_$$inter$0$Entry_correct)))))))
(let (($for.cond.backedge_correct (=> (and %lbl%+5098 true) (=> (or
p0$1@3
p0$2@3) (and
(or %lbl%@14291 (=> (= (ControlFlow 0 5098) (- 0 14291)) (=> _READ_HAS_OCCURRED_$$input$1@1 (= _READ_SOURCE_$$input$1@1 #x00000006))))
(=> (=> _READ_HAS_OCCURRED_$$input$1@1 (= _READ_SOURCE_$$input$1@1 #x00000006)) (and
(or %lbl%@14299 (=> (= (ControlFlow 0 5098) (- 0 14299)) (=> _WRITE_HAS_OCCURRED_$$input$1 false)))
(=> (=> _WRITE_HAS_OCCURRED_$$input$1 false) (and
(or %lbl%@14305 (=> (= (ControlFlow 0 5098) (- 0 14305)) (=> (not _READ_HAS_OCCURRED_$$input$1@1) (= _READ_SOURCE_$$input$1@1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$input$1@1) (= _READ_SOURCE_$$input$1@1 #x00000000)) (and
(or %lbl%@14315 (=> (= (ControlFlow 0 5098) (- 0 14315)) (=> (not _WRITE_HAS_OCCURRED_$$input$1) (= _WRITE_SOURCE_$$input$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$input$1) (= _WRITE_SOURCE_$$input$1 #x00000000)) (and
(or %lbl%@14327 (=> (= (ControlFlow 0 5098) (- 0 14327)) (=> _READ_HAS_OCCURRED_$$dct8x8$1@1 (or
(= _READ_SOURCE_$$dct8x8$1@1 #x00000004)
(= _READ_SOURCE_$$dct8x8$1@1 #x00000005)))))
(=> (=> _READ_HAS_OCCURRED_$$dct8x8$1@1 (or
(= _READ_SOURCE_$$dct8x8$1@1 #x00000004)
(= _READ_SOURCE_$$dct8x8$1@1 #x00000005))) (and
(or %lbl%@14342 (=> (= (ControlFlow 0 5098) (- 0 14342)) (=> _WRITE_HAS_OCCURRED_$$dct8x8$1 false)))
(=> (=> _WRITE_HAS_OCCURRED_$$dct8x8$1 false) (and
(or %lbl%@14348 (=> (= (ControlFlow 0 5098) (- 0 14348)) (=> (not _READ_HAS_OCCURRED_$$dct8x8$1@1) (= _READ_SOURCE_$$dct8x8$1@1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$dct8x8$1@1) (= _READ_SOURCE_$$dct8x8$1@1 #x00000000)) (and
(or %lbl%@14358 (=> (= (ControlFlow 0 5098) (- 0 14358)) (=> (not _WRITE_HAS_OCCURRED_$$dct8x8$1) (= _WRITE_SOURCE_$$dct8x8$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$dct8x8$1) (= _WRITE_SOURCE_$$dct8x8$1 #x00000000)) (and
(or %lbl%@14370 (=> (= (ControlFlow 0 5098) (- 0 14370)) (=> _READ_HAS_OCCURRED_$$output$1 false)))
(=> (=> _READ_HAS_OCCURRED_$$output$1 false) (and
(or %lbl%@14376 (=> (= (ControlFlow 0 5098) (- 0 14376)) (=> _WRITE_HAS_OCCURRED_$$output$1 (= _WRITE_SOURCE_$$output$1 #x00000002))))
(=> (=> _WRITE_HAS_OCCURRED_$$output$1 (= _WRITE_SOURCE_$$output$1 #x00000002)) (and
(or %lbl%@14386 (=> (= (ControlFlow 0 5098) (- 0 14386)) (=> (not _READ_HAS_OCCURRED_$$output$1) (= _READ_SOURCE_$$output$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$output$1) (= _READ_SOURCE_$$output$1 #x00000000)) (and
(or %lbl%@14398 (=> (= (ControlFlow 0 5098) (- 0 14398)) (=> (not _WRITE_HAS_OCCURRED_$$output$1) (= _WRITE_SOURCE_$$output$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$output$1) (= _WRITE_SOURCE_$$output$1 #x00000000)) (and
(or %lbl%@14410 (=> (= (ControlFlow 0 5098) (- 0 14410)) (=> _READ_HAS_OCCURRED_$$inter$1 (= _READ_SOURCE_$$inter$1 #x00000003))))
(=> (=> _READ_HAS_OCCURRED_$$inter$1 (= _READ_SOURCE_$$inter$1 #x00000003)) (and
(or %lbl%@14420 (=> (= (ControlFlow 0 5098) (- 0 14420)) (=> _WRITE_HAS_OCCURRED_$$inter$1 (= _WRITE_SOURCE_$$inter$1 #x00000001))))
(=> (=> _WRITE_HAS_OCCURRED_$$inter$1 (= _WRITE_SOURCE_$$inter$1 #x00000001)) (and
(or %lbl%@14430 (=> (= (ControlFlow 0 5098) (- 0 14430)) (=> (not _READ_HAS_OCCURRED_$$inter$1) (= _READ_SOURCE_$$inter$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$inter$1) (= _READ_SOURCE_$$inter$1 #x00000000)) (and
(or %lbl%@14442 (=> (= (ControlFlow 0 5098) (- 0 14442)) (=> (not _WRITE_HAS_OCCURRED_$$inter$1) (= _WRITE_SOURCE_$$inter$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$inter$1) (= _WRITE_SOURCE_$$inter$1 #x00000000)) (and
(or %lbl%@14454 (=> (= (ControlFlow 0 5098) (- 0 14454)) (=> p0$1@3 _P$1@@0)))
(=> (=> p0$1@3 _P$1@@0) (and
(or %lbl%@14459 (=> (= (ControlFlow 0 5098) (- 0 14459)) (=> p0$2@3 _P$2@@0)))
(=> (=> p0$2@3 _P$2@@0) true))))))))))))))))))))))))))))))))))))))))
(let (($for.cond$2_correct (=> (and %lbl%+4283 true) (and
(or %lbl%@14189 (=> (= (ControlFlow 0 4283) (- 0 14189)) (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$input$1
(= _WRITE_OFFSET_$$input$1 call1785formal@$ret$2@0)))))
(=> (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$input$1
(= _WRITE_OFFSET_$$input$1 call1785formal@$ret$2@0))) (=> (and
(= $acc.0$1@2 (ite p1$1@1 (FADD32 $acc.0$1@1 (FMUL32 v6$1@1 v7$1@1)) $acc.0$1@1))
(= $acc.0$2@2 (ite p1$2@1 (FADD32 $acc.0$2@1 (FMUL32 v6$2@1 v7$2@1)) $acc.0$2@1))
(= $k.0$1@2 (ite p1$1@1 (bvadd $k.0$1@1 #x00000001) $k.0$1@1))
(= $k.0$2@2 (ite p1$2@1 (bvadd $k.0$2@1 #x00000001) $k.0$2@1))
(= p0$1@3 (ite p1$1@1 true p0$1@2))
(= p0$2@3 (ite p1$2@1 true p0$2@2))) (and
(=> (= (ControlFlow 0 4283) 5098) $for.cond.backedge_correct)
(=> (= (ControlFlow 0 4283) 4365) $for.cond.tail_correct))))))))
(let ((inline$_LOG_READ_$$input$0$_LOG_READ_correct (=> (and %lbl%+4277 true) (=> (and
(= _READ_HAS_OCCURRED_$$input$1@1 (ite (and
p1$1@1
inline$_LOG_READ_$$input$0$track@1) true _READ_HAS_OCCURRED_$$input$1@0))
(= _READ_OFFSET_$$input$1@1 (ite (and
p1$1@1
inline$_LOG_READ_$$input$0$track@1) call1785formal@$ret$1@0 _READ_OFFSET_$$input$1@0))
(= _READ_SOURCE_$$input$1@1 (ite (and
p1$1@1
inline$_LOG_READ_$$input$0$track@1) #x00000006 _READ_SOURCE_$$input$1@0))
(= (ControlFlow 0 4277) 4283)) $for.cond$2_correct))))
(let (($for.cond$1_correct (=> (and %lbl%+4281 true) (and
(or %lbl%@14080 (=> (= (ControlFlow 0 4281) (- 0 14080)) (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$dct8x8$1
(= _WRITE_OFFSET_$$dct8x8$1 $cond$2@2)))))
(=> (not (and
p1$2@1
_WRITE_HAS_OCCURRED_$$dct8x8$1
(= _WRITE_OFFSET_$$dct8x8$1 $cond$2@2))) (and
(or %lbl%@14094 (=> (= (ControlFlow 0 4281) (- 0 14094)) (=> p1$1@1 true)))
(=> (=> p1$1@1 true) (=> (and
(= v7$1@1 (ite p1$1@1 _HAVOC_bv32$1@2 v7$1@0))
(= v7$2@1 (ite p1$2@1 _HAVOC_bv32$2@2 v7$2@0))
(= (ControlFlow 0 4281) 4277)) inline$_LOG_READ_$$input$0$_LOG_READ_correct))))))))
(let ((inline$_LOG_READ_$$dct8x8$0$_LOG_READ_correct (=> (and %lbl%+4195 true) (=> (and
(= _READ_HAS_OCCURRED_$$dct8x8$1@1 (ite (and
p1$1@1
inline$_LOG_READ_$$dct8x8$0$track@1) true _READ_HAS_OCCURRED_$$dct8x8$1@0))
(= _READ_OFFSET_$$dct8x8$1@1 (ite (and
p1$1@1
inline$_LOG_READ_$$dct8x8$0$track@1) $cond$1@2 _READ_OFFSET_$$dct8x8$1@0))
(= _READ_SOURCE_$$dct8x8$1@1 (ite (and
p1$1@1
inline$_LOG_READ_$$dct8x8$0$track@1) #x00000005 _READ_SOURCE_$$dct8x8$1@0))
(= (ControlFlow 0 4195) 4281)) $for.cond$1_correct))))
(let (($for.cond_correct (=> (and %lbl%+4199 true) (=> (and
(=> _READ_HAS_OCCURRED_$$input$1@0 (= _READ_SOURCE_$$input$1@0 #x00000006))
(=> _WRITE_HAS_OCCURRED_$$input$1 false)) (=> (and
(=> (not _READ_HAS_OCCURRED_$$input$1@0) (= _READ_SOURCE_$$input$1@0 #x00000000))
(=> (not _WRITE_HAS_OCCURRED_$$input$1) (= _WRITE_SOURCE_$$input$1 #x00000000))
(=> _READ_HAS_OCCURRED_$$dct8x8$1@0 (or
(= _READ_SOURCE_$$dct8x8$1@0 #x00000004)
(= _READ_SOURCE_$$dct8x8$1@0 #x00000005)))
(=> _WRITE_HAS_OCCURRED_$$dct8x8$1 false)
(=> (not _READ_HAS_OCCURRED_$$dct8x8$1@0) (= _READ_SOURCE_$$dct8x8$1@0 #x00000000))
(=> (not _WRITE_HAS_OCCURRED_$$dct8x8$1) (= _WRITE_SOURCE_$$dct8x8$1 #x00000000))
(=> _READ_HAS_OCCURRED_$$output$1 false)
(=> _WRITE_HAS_OCCURRED_$$output$1 (= _WRITE_SOURCE_$$output$1 #x00000002))
(=> (not _READ_HAS_OCCURRED_$$output$1) (= _READ_SOURCE_$$output$1 #x00000000))
(=> (not _WRITE_HAS_OCCURRED_$$output$1) (= _WRITE_SOURCE_$$output$1 #x00000000))
(=> _READ_HAS_OCCURRED_$$inter$1 (= _READ_SOURCE_$$inter$1 #x00000003))
(=> _WRITE_HAS_OCCURRED_$$inter$1 (= _WRITE_SOURCE_$$inter$1 #x00000001))
(=> (not _READ_HAS_OCCURRED_$$inter$1) (= _READ_SOURCE_$$inter$1 #x00000000))
(=> (not _WRITE_HAS_OCCURRED_$$inter$1) (= _WRITE_SOURCE_$$inter$1 #x00000000))
(=> p0$1@1 _P$1@@0)
(=> p0$2@1 _P$2@@0)
(= v3$1@1 (ite p0$1@1 (bvult $k.0$1@1 $blockWidth$1@@0) v3$1@0))
(= v3$2@1 (ite p0$2@1 (bvult $k.0$2@1 $blockWidth$2@@0) v3$2@0))
(= p1$1@1 (ite p0$1@1 v3$1@1 false))
(= p1$2@1 (ite p0$2@1 v3$2@1 false))
(= p0$1@2 (ite p0$1@1 v3$1@1 p0$1@1))
(= p0$2@2 (ite p0$2@1 v3$2@1 p0$2@1))
(= v4$1@1 (ite p1$1@1 (not (= $inverse$1 #x00000000)) v4$1@0))
(= v4$2@1 (ite p1$2@1 (not (= $inverse$2 #x00000000)) v4$2@0))
(= p3$1@1 (ite p1$1@1 v4$1@1 false))
(= p3$2@1 (ite p1$2@1 v4$2@1 false))
(= p2$1@1 (ite p1$1@1 (not v4$1@1) false))
(= p2$2@1 (ite p1$2@1 (not v4$2@1) false))
(= $cond$1@1 (ite p2$1@1 (bvadd (bvmul $k.0$1@1 $blockWidth$1@@0) v0$1@0) $cond$1@0))
(= $cond$2@1 (ite p2$2@1 (bvadd (bvmul $k.0$2@1 $blockWidth$2@@0) v0$2@0) $cond$2@0))
(= $cond$1@2 (ite p3$1@1 (bvadd (bvmul v0$1@0 $blockWidth$1@@0) $k.0$1@1) $cond$1@1))
(= $cond$2@2 (ite p3$2@1 (bvadd (bvmul v0$2@0 $blockWidth$2@@0) $k.0$2@1) $cond$2@1))) (and
(or %lbl%@13261 (=> (= (ControlFlow 0 4199) (- 0 13261)) (bvsgt group_size_x #x00000000)))
(=> (bvsgt group_size_x #x00000000) (and
(or %lbl%@13267 (=> (= (ControlFlow 0 4199) (- 0 13267)) (bvsgt num_groups_x #x00000000)))
(=> (bvsgt num_groups_x #x00000000) (and
(or %lbl%@13273 (=> (= (ControlFlow 0 4199) (- 0 13273)) (bvsge group_id_x$1 #x00000000)))
(=> (bvsge group_id_x$1 #x00000000) (and
(or %lbl%@13279 (=> (= (ControlFlow 0 4199) (- 0 13279)) (bvsge group_id_x$2 #x00000000)))
(=> (bvsge group_id_x$2 #x00000000) (and
(or %lbl%@13285 (=> (= (ControlFlow 0 4199) (- 0 13285)) (bvslt group_id_x$1 num_groups_x)))
(=> (bvslt group_id_x$1 num_groups_x) (and
(or %lbl%@13291 (=> (= (ControlFlow 0 4199) (- 0 13291)) (bvslt group_id_x$2 num_groups_x)))
(=> (bvslt group_id_x$2 num_groups_x) (and
(or %lbl%@13297 (=> (= (ControlFlow 0 4199) (- 0 13297)) (bvsge local_id_x$1 #x00000000)))
(=> (bvsge local_id_x$1 #x00000000) (and
(or %lbl%@13303 (=> (= (ControlFlow 0 4199) (- 0 13303)) (bvsge local_id_x$2 #x00000000)))
(=> (bvsge local_id_x$2 #x00000000) (and
(or %lbl%@13309 (=> (= (ControlFlow 0 4199) (- 0 13309)) (bvslt local_id_x$1 group_size_x)))
(=> (bvslt local_id_x$1 group_size_x) (and
(or %lbl%@13315 (=> (= (ControlFlow 0 4199) (- 0 13315)) (bvslt local_id_x$2 group_size_x)))
(=> (bvslt local_id_x$2 group_size_x) (and
(or %lbl%@13321 (=> (= (ControlFlow 0 4199) (- 0 13321)) (bvsgt group_size_y #x00000000)))
(=> (bvsgt group_size_y #x00000000) (and
(or %lbl%@13327 (=> (= (ControlFlow 0 4199) (- 0 13327)) (bvsgt num_groups_y #x00000000)))
(=> (bvsgt num_groups_y #x00000000) (and
(or %lbl%@13333 (=> (= (ControlFlow 0 4199) (- 0 13333)) (bvsge group_id_y$1 #x00000000)))
(=> (bvsge group_id_y$1 #x00000000) (and
(or %lbl%@13339 (=> (= (ControlFlow 0 4199) (- 0 13339)) (bvsge group_id_y$2 #x00000000)))
(=> (bvsge group_id_y$2 #x00000000) (and
(or %lbl%@13345 (=> (= (ControlFlow 0 4199) (- 0 13345)) (bvslt group_id_y$1 num_groups_y)))
(=> (bvslt group_id_y$1 num_groups_y) (and
(or %lbl%@13351 (=> (= (ControlFlow 0 4199) (- 0 13351)) (bvslt group_id_y$2 num_groups_y)))
(=> (bvslt group_id_y$2 num_groups_y) (and
(or %lbl%@13357 (=> (= (ControlFlow 0 4199) (- 0 13357)) (bvsge local_id_y$1 #x00000000)))
(=> (bvsge local_id_y$1 #x00000000) (and
(or %lbl%@13363 (=> (= (ControlFlow 0 4199) (- 0 13363)) (bvsge local_id_y$2 #x00000000)))
(=> (bvsge local_id_y$2 #x00000000) (and
(or %lbl%@13369 (=> (= (ControlFlow 0 4199) (- 0 13369)) (bvslt local_id_y$1 group_size_y)))
(=> (bvslt local_id_y$1 group_size_y) (and
(or %lbl%@13375 (=> (= (ControlFlow 0 4199) (- 0 13375)) (bvslt local_id_y$2 group_size_y)))
(=> (bvslt local_id_y$2 group_size_y) (and
(or %lbl%@13381 (=> (= (ControlFlow 0 4199) (- 0 13381)) (bvsgt group_size_z #x00000000)))
(=> (bvsgt group_size_z #x00000000) (and
(or %lbl%@13387 (=> (= (ControlFlow 0 4199) (- 0 13387)) (bvsgt num_groups_z #x00000000)))
(=> (bvsgt num_groups_z #x00000000) (and
(or %lbl%@13393 (=> (= (ControlFlow 0 4199) (- 0 13393)) (bvsge group_id_z$1 #x00000000)))
(=> (bvsge group_id_z$1 #x00000000) (and
(or %lbl%@13399 (=> (= (ControlFlow 0 4199) (- 0 13399)) (bvsge group_id_z$2 #x00000000)))
(=> (bvsge group_id_z$2 #x00000000) (and
(or %lbl%@13405 (=> (= (ControlFlow 0 4199) (- 0 13405)) (bvslt group_id_z$1 num_groups_z)))
(=> (bvslt group_id_z$1 num_groups_z) (and
(or %lbl%@13411 (=> (= (ControlFlow 0 4199) (- 0 13411)) (bvslt group_id_z$2 num_groups_z)))
(=> (bvslt group_id_z$2 num_groups_z) (and
(or %lbl%@13417 (=> (= (ControlFlow 0 4199) (- 0 13417)) (bvsge local_id_z$1 #x00000000)))
(=> (bvsge local_id_z$1 #x00000000) (and
(or %lbl%@13423 (=> (= (ControlFlow 0 4199) (- 0 13423)) (bvsge local_id_z$2 #x00000000)))
(=> (bvsge local_id_z$2 #x00000000) (and
(or %lbl%@13429 (=> (= (ControlFlow 0 4199) (- 0 13429)) (bvslt local_id_z$1 group_size_z)))
(=> (bvslt local_id_z$1 group_size_z) (and
(or %lbl%@13435 (=> (= (ControlFlow 0 4199) (- 0 13435)) (bvslt local_id_z$2 group_size_z)))
(=> (bvslt local_id_z$2 group_size_z) (and
(or %lbl%@13441 (=> (= (ControlFlow 0 4199) (- 0 13441)) (=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (or
(not (= local_id_x$1 local_id_x$2))
(not (= local_id_y$1 local_id_y$2))
(not (= local_id_z$1 local_id_z$2))))))
(=> (=> (and
(= group_id_x$1 group_id_x$2)
(= group_id_y$1 group_id_y$2)
(= group_id_z$1 group_id_z$2)) (or
(not (= local_id_x$1 local_id_x$2))
(not (= local_id_y$1 local_id_y$2))
(not (= local_id_z$1 local_id_z$2)))) (and
(or %lbl%@13487 (=> (= (ControlFlow 0 4199) (- 0 13487)) (=> _b0 (= p1$1@1 p1$2@1))))
(=> (=> _b0 (= p1$1@1 p1$2@1)) (and
(or %lbl%@13495 (=> (= (ControlFlow 0 4199) (- 0 13495)) (=> _b1 (=> (and
p1$1@1
p1$2@1) (= group_id_x$1 group_id_x$2)))))
(=> (=> _b1 (=> (and
p1$1@1
p1$2@1) (= group_id_x$1 group_id_x$2))) (and
(or %lbl%@13509 (=> (= (ControlFlow 0 4199) (- 0 13509)) (=> _b2 (= group_id_x$1 group_id_x$2))))
(=> (=> _b2 (= group_id_x$1 group_id_x$2)) (and
(or %lbl%@13517 (=> (= (ControlFlow 0 4199) (- 0 13517)) (=> _b3 (=> (and
p1$1@1
p1$2@1) (= group_id_y$1 group_id_y$2)))))
(=> (=> _b3 (=> (and
p1$1@1
p1$2@1) (= group_id_y$1 group_id_y$2))) (and
(or %lbl%@13531 (=> (= (ControlFlow 0 4199) (- 0 13531)) (=> _b4 (= group_id_y$1 group_id_y$2))))
(=> (=> _b4 (= group_id_y$1 group_id_y$2)) (and
(or %lbl%@13539 (=> (= (ControlFlow 0 4199) (- 0 13539)) (=> _b5 (=> (and
p1$1@1
p1$2@1) (= v1$1@0 v1$2@0)))))
(=> (=> _b5 (=> (and
p1$1@1
p1$2@1) (= v1$1@0 v1$2@0))) (and
(or %lbl%@13553 (=> (= (ControlFlow 0 4199) (- 0 13553)) (=> _b6 (= v1$1@0 v1$2@0))))
(=> (=> _b6 (= v1$1@0 v1$2@0)) (and
(or %lbl%@13561 (=> (= (ControlFlow 0 4199) (- 0 13561)) (=> _b7 (=> (and
p1$1@1
p1$2@1) (= $k.0$1@1 $k.0$2@1)))))
(=> (=> _b7 (=> (and
p1$1@1
p1$2@1) (= $k.0$1@1 $k.0$2@1))) (and
(or %lbl%@13575 (=> (= (ControlFlow 0 4199) (- 0 13575)) (=> _b8 (= $k.0$1@1 $k.0$2@1))))
(=> (=> _b8 (= $k.0$1@1 $k.0$2@1)) (and
(or %lbl%@13583 (=> (= (ControlFlow 0 4199) (- 0 13583)) (=> _b9 (=> (and
p1$1@1
p1$2@1) (= $blockWidth$1@@0 $blockWidth$2@@0)))))
(=> (=> _b9 (=> (and
p1$1@1
p1$2@1) (= $blockWidth$1@@0 $blockWidth$2@@0))) (and
(or %lbl%@13597 (=> (= (ControlFlow 0 4199) (- 0 13597)) (=> _b10 (= $blockWidth$1@@0 $blockWidth$2@@0))))
(=> (=> _b10 (= $blockWidth$1@@0 $blockWidth$2@@0)) (and
(or %lbl%@13605 (=> (= (ControlFlow 0 4199) (- 0 13605)) (=> _b11 (=> (and
p1$1@1
p1$2@1) (= $width$1 $width$2)))))
(=> (=> _b11 (=> (and
p1$1@1
p1$2@1) (= $width$1 $width$2))) (and
(or %lbl%@13619 (=> (= (ControlFlow 0 4199) (- 0 13619)) (=> _b12 (= $width$1 $width$2))))
(=> (=> _b12 (= $width$1 $width$2)) (and
(or %lbl%@13627 (=> (= (ControlFlow 0 4199) (- 0 13627)) (=> _b13 (not _READ_HAS_OCCURRED_$$output$1))))
(=> (=> _b13 (not _READ_HAS_OCCURRED_$$output$1)) (and
(or %lbl%@13635 (=> (= (ControlFlow 0 4199) (- 0 13635)) (=> _b14 (not _WRITE_HAS_OCCURRED_$$output$1))))
(=> (=> _b14 (not _WRITE_HAS_OCCURRED_$$output$1)) (and
(or %lbl%@13643 (=> (= (ControlFlow 0 4199) (- 0 13643)) (=> _b15 (=> _WRITE_HAS_OCCURRED_$$output$1 (= _WRITE_OFFSET_$$output$1 local_id_x$1)))))
(=> (=> _b15 (=> _WRITE_HAS_OCCURRED_$$output$1 (= _WRITE_OFFSET_$$output$1 local_id_x$1))) (and
(or %lbl%@13657 (=> (= (ControlFlow 0 4199) (- 0 13657)) (=> _b16 (=> _READ_HAS_OCCURRED_$$output$1 (= _READ_OFFSET_$$output$1 local_id_x$1)))))
(=> (=> _b16 (=> _READ_HAS_OCCURRED_$$output$1 (= _READ_OFFSET_$$output$1 local_id_x$1))) (and
(or %lbl%@13671 (=> (= (ControlFlow 0 4199) (- 0 13671)) (=> _b17 (not _READ_HAS_OCCURRED_$$input$1@0))))
(=> (=> _b17 (not _READ_HAS_OCCURRED_$$input$1@0)) (and
(or %lbl%@13678 (=> (= (ControlFlow 0 4199) (- 0 13678)) (=> _b18 (not _WRITE_HAS_OCCURRED_$$input$1))))
(=> (=> _b18 (not _WRITE_HAS_OCCURRED_$$input$1)) (and
(or %lbl%@13686 (=> (= (ControlFlow 0 4199) (- 0 13686)) (=> _b19 (=> _WRITE_HAS_OCCURRED_$$input$1 (= _WRITE_OFFSET_$$input$1 local_id_x$1)))))
(=> (=> _b19 (=> _WRITE_HAS_OCCURRED_$$input$1 (= _WRITE_OFFSET_$$input$1 local_id_x$1))) (and
(or %lbl%@13700 (=> (= (ControlFlow 0 4199) (- 0 13700)) (=> _b20 (=> _READ_HAS_OCCURRED_$$input$1@0 (= _READ_OFFSET_$$input$1@0 local_id_x$1)))))
(=> (=> _b20 (=> _READ_HAS_OCCURRED_$$input$1@0 (= _READ_OFFSET_$$input$1@0 local_id_x$1))) (and
(or %lbl%@13712 (=> (= (ControlFlow 0 4199) (- 0 13712)) (=> _b21 (not _READ_HAS_OCCURRED_$$dct8x8$1@0))))
(=> (=> _b21 (not _READ_HAS_OCCURRED_$$dct8x8$1@0)) (and
(or %lbl%@13719 (=> (= (ControlFlow 0 4199) (- 0 13719)) (=> _b22 (not _WRITE_HAS_OCCURRED_$$dct8x8$1))))
(=> (=> _b22 (not _WRITE_HAS_OCCURRED_$$dct8x8$1)) (and
(or %lbl%@13727 (=> (= (ControlFlow 0 4199) (- 0 13727)) (=> _b23 (=> _WRITE_HAS_OCCURRED_$$dct8x8$1 (= _WRITE_OFFSET_$$dct8x8$1 local_id_x$1)))))
(=> (=> _b23 (=> _WRITE_HAS_OCCURRED_$$dct8x8$1 (= _WRITE_OFFSET_$$dct8x8$1 local_id_x$1))) (and
(or %lbl%@13741 (=> (= (ControlFlow 0 4199) (- 0 13741)) (=> _b24 (=> _READ_HAS_OCCURRED_$$dct8x8$1@0 (= _READ_OFFSET_$$dct8x8$1@0 local_id_x$1)))))
(=> (=> _b24 (=> _READ_HAS_OCCURRED_$$dct8x8$1@0 (= _READ_OFFSET_$$dct8x8$1@0 local_id_x$1))) (and
(or %lbl%@13753 (=> (= (ControlFlow 0 4199) (- 0 13753)) (=> _b25 (not _READ_HAS_OCCURRED_$$inter$1))))
(=> (=> _b25 (not _READ_HAS_OCCURRED_$$inter$1)) (and
(or %lbl%@13761 (=> (= (ControlFlow 0 4199) (- 0 13761)) (=> _b26 (not _WRITE_HAS_OCCURRED_$$inter$1))))
(=> (=> _b26 (not _WRITE_HAS_OCCURRED_$$inter$1)) (and
(or %lbl%@13769 (=> (= (ControlFlow 0 4199) (- 0 13769)) (=> _b27 (=> _WRITE_HAS_OCCURRED_$$inter$1 (= _WRITE_OFFSET_$$inter$1 local_id_x$1)))))
(=> (=> _b27 (=> _WRITE_HAS_OCCURRED_$$inter$1 (= _WRITE_OFFSET_$$inter$1 local_id_x$1))) (and
(or %lbl%@13783 (=> (= (ControlFlow 0 4199) (- 0 13783)) (=> _b28 (=> _READ_HAS_OCCURRED_$$inter$1 (= _READ_OFFSET_$$inter$1 local_id_x$1)))))
(=> (=> _b28 (=> _READ_HAS_OCCURRED_$$inter$1 (= _READ_OFFSET_$$inter$1 local_id_x$1))) (=> (=> _b29 (= call1785formal@$ret$1@0 call1785formal@$ret$2@0)) (=> (and
(=> _b30 (not _READ_HAS_OCCURRED_$$output$1))
(=> _b31 (not _WRITE_HAS_OCCURRED_$$output$1))
(=> _b32 (=> _WRITE_HAS_OCCURRED_$$output$1 (= _WRITE_OFFSET_$$output$1 local_id_x$1)))
(=> _b33 (=> _READ_HAS_OCCURRED_$$output$1 (= _READ_OFFSET_$$output$1 local_id_x$1)))
(=> _b34 (not _READ_HAS_OCCURRED_$$input$1@0))
(=> _b35 (not _WRITE_HAS_OCCURRED_$$input$1))
(=> _b36 (=> _WRITE_HAS_OCCURRED_$$input$1 (= _WRITE_OFFSET_$$input$1 local_id_x$1)))
(=> _b37 (=> _READ_HAS_OCCURRED_$$input$1@0 (= _READ_OFFSET_$$input$1@0 local_id_x$1)))
(=> _b38 (not _READ_HAS_OCCURRED_$$dct8x8$1@0))
(=> _b39 (not _WRITE_HAS_OCCURRED_$$dct8x8$1))
(=> _b40 (=> _WRITE_HAS_OCCURRED_$$dct8x8$1 (= _WRITE_OFFSET_$$dct8x8$1 local_id_x$1)))
(=> _b41 (=> _READ_HAS_OCCURRED_$$dct8x8$1@0 (= _READ_OFFSET_$$dct8x8$1@0 local_id_x$1)))
(=> _b42 (not _READ_HAS_OCCURRED_$$inter$1))
(=> _b43 (not _WRITE_HAS_OCCURRED_$$inter$1))
(=> _b44 (=> _WRITE_HAS_OCCURRED_$$inter$1 (= _WRITE_OFFSET_$$inter$1 local_id_x$1)))
(=> _b45 (=> _READ_HAS_OCCURRED_$$inter$1 (= _READ_OFFSET_$$inter$1 local_id_x$1)))) (and
(or %lbl%@13985 (=> (= (ControlFlow 0 4199) (- 0 13985)) (=> p1$1@1 true)))
(=> (=> p1$1@1 true) (=> (and
(= v6$1@1 (ite p1$1@1 _HAVOC_bv32$1@1 v6$1@0))
(= v6$2@1 (ite p1$2@1 _HAVOC_bv32$2@1 v6$2@0))
(= (ControlFlow 0 4199) 4195)) inline$_LOG_READ_$$dct8x8$0$_LOG_READ_correct))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(let (($entry_correct@@0 (=> (and %lbl%+4117 true) (=> (and
(= v0$1@0 (ite _P$1@@0 local_id_x$1 v0$1))
(= v0$2@0 (ite _P$2@@0 local_id_x$2 v0$2))) (=> (and
(= v1$1@0 (ite _P$1@@0 local_id_y$1 v1$1))
(= v1$2@0 (ite _P$2@@0 local_id_y$2 v1$2))
(= v2$1@0 (ite _P$1@@0 (bvadd (bvmul (bvadd (bvmul group_size_y group_id_y$1) local_id_y$1) $width$1) (bvadd (bvmul group_size_x group_id_x$1) local_id_x$1)) v2$1))
(= v2$2@0 (ite _P$2@@0 (bvadd (bvmul (bvadd (bvmul group_size_y group_id_y$2) local_id_y$2) $width$2) (bvadd (bvmul group_size_x group_id_x$2) local_id_x$2)) v2$2))) (=> (and
(= $acc.0$1@0 (ite _P$1@@0 #x00000000 $acc.0$1))
(= $acc.0$2@0 (ite _P$2@@0 #x00000000 $acc.0$2))
(= $k.0$1@0 (ite _P$1@@0 #x00000000 $k.0$1))
(= $k.0$2@0 (ite _P$2@@0 #x00000000 $k.0$2))
(= p0$1@0 (ite _P$1@@0 true false))
(= p0$2@0 (ite _P$2@@0 true false))) (and
(or %lbl%@12497 (=> (= (ControlFlow 0 4117) (- 0 12497)) (=> _READ_HAS_OCCURRED_$$input$1 (= _READ_SOURCE_$$input$1 #x00000006))))
(=> (=> _READ_HAS_OCCURRED_$$input$1 (= _READ_SOURCE_$$input$1 #x00000006)) (and
(or %lbl%@12507 (=> (= (ControlFlow 0 4117) (- 0 12507)) (=> _WRITE_HAS_OCCURRED_$$input$1 false)))
(=> (=> _WRITE_HAS_OCCURRED_$$input$1 false) (and
(or %lbl%@12513 (=> (= (ControlFlow 0 4117) (- 0 12513)) (=> (not _READ_HAS_OCCURRED_$$input$1) (= _READ_SOURCE_$$input$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$input$1) (= _READ_SOURCE_$$input$1 #x00000000)) (and
(or %lbl%@12525 (=> (= (ControlFlow 0 4117) (- 0 12525)) (=> (not _WRITE_HAS_OCCURRED_$$input$1) (= _WRITE_SOURCE_$$input$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$input$1) (= _WRITE_SOURCE_$$input$1 #x00000000)) (and
(or %lbl%@12537 (=> (= (ControlFlow 0 4117) (- 0 12537)) (=> _READ_HAS_OCCURRED_$$dct8x8$1 (or
(= _READ_SOURCE_$$dct8x8$1 #x00000004)
(= _READ_SOURCE_$$dct8x8$1 #x00000005)))))
(=> (=> _READ_HAS_OCCURRED_$$dct8x8$1 (or
(= _READ_SOURCE_$$dct8x8$1 #x00000004)
(= _READ_SOURCE_$$dct8x8$1 #x00000005))) (and
(or %lbl%@12555 (=> (= (ControlFlow 0 4117) (- 0 12555)) (=> _WRITE_HAS_OCCURRED_$$dct8x8$1 false)))
(=> (=> _WRITE_HAS_OCCURRED_$$dct8x8$1 false) (and
(or %lbl%@12561 (=> (= (ControlFlow 0 4117) (- 0 12561)) (=> (not _READ_HAS_OCCURRED_$$dct8x8$1) (= _READ_SOURCE_$$dct8x8$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$dct8x8$1) (= _READ_SOURCE_$$dct8x8$1 #x00000000)) (and
(or %lbl%@12573 (=> (= (ControlFlow 0 4117) (- 0 12573)) (=> (not _WRITE_HAS_OCCURRED_$$dct8x8$1) (= _WRITE_SOURCE_$$dct8x8$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$dct8x8$1) (= _WRITE_SOURCE_$$dct8x8$1 #x00000000)) (and
(or %lbl%@12585 (=> (= (ControlFlow 0 4117) (- 0 12585)) (=> _READ_HAS_OCCURRED_$$output$1 false)))
(=> (=> _READ_HAS_OCCURRED_$$output$1 false) (and
(or %lbl%@12591 (=> (= (ControlFlow 0 4117) (- 0 12591)) (=> _WRITE_HAS_OCCURRED_$$output$1 (= _WRITE_SOURCE_$$output$1 #x00000002))))
(=> (=> _WRITE_HAS_OCCURRED_$$output$1 (= _WRITE_SOURCE_$$output$1 #x00000002)) (and
(or %lbl%@12601 (=> (= (ControlFlow 0 4117) (- 0 12601)) (=> (not _READ_HAS_OCCURRED_$$output$1) (= _READ_SOURCE_$$output$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$output$1) (= _READ_SOURCE_$$output$1 #x00000000)) (and
(or %lbl%@12613 (=> (= (ControlFlow 0 4117) (- 0 12613)) (=> (not _WRITE_HAS_OCCURRED_$$output$1) (= _WRITE_SOURCE_$$output$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$output$1) (= _WRITE_SOURCE_$$output$1 #x00000000)) (and
(or %lbl%@12625 (=> (= (ControlFlow 0 4117) (- 0 12625)) (=> _READ_HAS_OCCURRED_$$inter$1 (= _READ_SOURCE_$$inter$1 #x00000003))))
(=> (=> _READ_HAS_OCCURRED_$$inter$1 (= _READ_SOURCE_$$inter$1 #x00000003)) (and
(or %lbl%@12635 (=> (= (ControlFlow 0 4117) (- 0 12635)) (=> _WRITE_HAS_OCCURRED_$$inter$1 (= _WRITE_SOURCE_$$inter$1 #x00000001))))
(=> (=> _WRITE_HAS_OCCURRED_$$inter$1 (= _WRITE_SOURCE_$$inter$1 #x00000001)) (and
(or %lbl%@12645 (=> (= (ControlFlow 0 4117) (- 0 12645)) (=> (not _READ_HAS_OCCURRED_$$inter$1) (= _READ_SOURCE_$$inter$1 #x00000000))))
(=> (=> (not _READ_HAS_OCCURRED_$$inter$1) (= _READ_SOURCE_$$inter$1 #x00000000)) (and
(or %lbl%@12657 (=> (= (ControlFlow 0 4117) (- 0 12657)) (=> (not _WRITE_HAS_OCCURRED_$$inter$1) (= _WRITE_SOURCE_$$inter$1 #x00000000))))
(=> (=> (not _WRITE_HAS_OCCURRED_$$inter$1) (= _WRITE_SOURCE_$$inter$1 #x00000000)) (and
(or %lbl%@12669 (=> (= (ControlFlow 0 4117) (- 0 12669)) (=> p0$1@0 _P$1@@0)))
(=> (=> p0$1@0 _P$1@@0) (and
(or %lbl%@12674 (=> (= (ControlFlow 0 4117) (- 0 12674)) (=> p0$2@0 _P$2@@0)))
(=> (=> p0$2@0 _P$2@@0) (=> (= (ControlFlow 0 4117) 4199) $for.cond_correct)))))))))))))))))))))))))))))))))))))))))))
(let ((PreconditionGeneratedEntry_correct@@0 (=> (and %lbl%+11167 true) (=> (and
(not (= (ite (= $width$1 (bvmul group_size_x num_groups_x)) #b1 #b0) #b0))
(not (= (ite (= $width$2 (bvmul group_size_x num_groups_x)) #b1 #b0) #b0))
(not (= (ite (= $blockWidth$1@@0 group_size_x) #b1 #b0) #b0))
(not (= (ite (= $blockWidth$2@@0 group_size_x) #b1 #b0) #b0))
(not _READ_HAS_OCCURRED_$$output$1)
(not _WRITE_HAS_OCCURRED_$$output$1)
(= _READ_SOURCE_$$output$1 #x00000000)
(= _WRITE_SOURCE_$$output$1 #x00000000)) (=> (and
(not _READ_HAS_OCCURRED_$$input$1)
(not _WRITE_HAS_OCCURRED_$$input$1)
(= _READ_SOURCE_$$input$1 #x00000000)
(= _WRITE_SOURCE_$$input$1 #x00000000)
(not _READ_HAS_OCCURRED_$$dct8x8$1)
(not _WRITE_HAS_OCCURRED_$$dct8x8$1)
(= _READ_SOURCE_$$dct8x8$1 #x00000000)
(= _WRITE_SOURCE_$$dct8x8$1 #x00000000)
(not _READ_HAS_OCCURRED_$$inter$1)
(not _WRITE_HAS_OCCURRED_$$inter$1)
(= _READ_SOURCE_$$inter$1 #x00000000)
(= _WRITE_SOURCE_$$inter$1 #x00000000)
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
(= _P$1@@0 _P$2@@0)
(= $width$1 $width$2)
(= $blockWidth$1@@0 $blockWidth$2@@0)
(= $inverse$1 $inverse$2)
(= (ControlFlow 0 11167) 4117)) $entry_correct@@0))))))
PreconditionGeneratedEntry_correct@@0)))))))))))))))))))))))))))))))))))))))
(push 1)
;(set-info :boogie-vc-id $getIdx)
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
_b11
_b12
_b13
_b14
_b15
_b16
_b17
_b18
_b19
_b20
_b21
_b22
_b23
_b24
_b25
_b26
_b27
_b28
_b29
_b30
_b31
_b32
_b33
_b34
_b35
_b36
_b37
_b38
_b39
_b40
_b41
_b42
_b43
_b44
_b45) $getIdx)
))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 9318)))
;(get-value ((ControlFlow 0 823)))
(assert (not (= (ControlFlow 0 823) (- 10729))))
(check-sat)
(pop 1)
(push 1)
;(set-info :boogie-vc-id $getIdx)
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
_b11
_b12
_b13
_b14
_b15
_b16
_b17
_b18
_b19
_b20
_b21
_b22
_b23
_b24
_b25
_b26
_b27
_b28
(not _b29)
_b30
_b31
_b32
_b33
_b34
_b35
_b36
_b37
_b38
_b39
_b40
_b41
_b42
_b43
_b44
_b45) $getIdx)
))
(check-sat)
(pop 1)
(push 1)
;(set-info :boogie-vc-id $DCT)
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
_b11
_b12
_b13
_b14
_b15
_b16
_b17
_b18
_b19
_b20
_b21
_b22
_b23
_b24
_b25
_b26
_b27
_b28
(not _b29)
_b30
_b31
_b32
_b33
_b34
_b35
_b36
_b37
_b38
_b39
_b40
_b41
_b42
_b43
_b44
_b45) $DCT)
))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 11167)))
;(get-value ((ControlFlow 0 4117)))
;(get-value ((ControlFlow 0 4199)))
(assert (not (= (ControlFlow 0 4199) (- 13495))))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 11167)))
;(get-value ((ControlFlow 0 4117)))
;(get-value ((ControlFlow 0 4199)))
(assert (not (= (ControlFlow 0 4199) (- 13487))))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 11167)))
;(get-value ((ControlFlow 0 4117)))
;(get-value ((ControlFlow 0 4199)))
(assert (not (= (ControlFlow 0 4199) (- 13509))))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 11167)))
;(get-value ((ControlFlow 0 4117)))
;(get-value ((ControlFlow 0 4199)))
(assert (not (= (ControlFlow 0 4199) (- 13553))))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 11167)))
;(get-value ((ControlFlow 0 4117)))
;(get-value ((ControlFlow 0 4199)))
(pop 1)
(push 1)
;(set-info :boogie-vc-id $DCT)
(assert (not
(=> (and
true
(not _b0)
(not _b1)
(not _b2)
_b3
_b4
_b5
(not _b6)
_b7
_b8
_b9
_b10
_b11
_b12
_b13
_b14
_b15
_b16
(not _b17)
_b18
_b19
_b20
_b21
_b22
_b23
_b24
_b25
_b26
_b27
_b28
(not _b29)
_b30
_b31
_b32
_b33
_b34
_b35
_b36
_b37
_b38
_b39
_b40
_b41
_b42
_b43
_b44
_b45) $DCT)
))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 11167)))
;(get-value ((ControlFlow 0 4117)))
;(get-value ((ControlFlow 0 4199)))
(assert (not (= (ControlFlow 0 4199) (- 13575))))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 11167)))
;(get-value ((ControlFlow 0 4117)))
;(get-value ((ControlFlow 0 4199)))
(assert (not (= (ControlFlow 0 4199) (- 13712))))
(check-sat)
;(get-value ((ControlFlow 0 0)))
;(get-value ((ControlFlow 0 11167)))
;(get-value ((ControlFlow 0 4117)))
;(get-value ((ControlFlow 0 4199)))
(assert (not (= (ControlFlow 0 4199) (- 13700))))
(check-sat)
