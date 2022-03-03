; COMMAND-LINE: --fmf-fun-rlv
; EXPECT: sat
; DISABLE-TESTER: model
(set-info :smt-lib-version 2.6)
(set-option :produce-models true)
(set-logic ALL)
(declare-datatypes ((a0 0)(a1 0)(a2 0)(a3 0)(a4 0)(a5 0)(a6 0)(a7 0)) (((c0$0) (c0$1 (c0$1$0 String) (c0$1$1 Int)) (c0$2 (c0$2$0 Bool) (c0$2$1 Int) (c0$2$2 String)))((c1$0) (c1$1) (c1$2))((c2$0 (c2$0$0 Int) (c2$0$1 a0) (c2$0$2 String) (c2$0$3 a3) (c2$0$4 String) (c2$0$5 Bool)))((c3$0 (c3$0$0 a7) (c3$0$1 a1) (c3$0$2 a5) (c3$0$3 a6) (c3$0$4 Int) (c3$0$5 Bool) (c3$0$6 Bool)) (c3$1 (c3$1$0 String)))((c4$0 (c4$0$0 String) (c4$0$1 a2) (c4$0$2 String)) (c4$1 (c4$1$0 a0) (c4$1$1 a4) (c4$1$2 a4) (c4$1$3 a7)) (c4$2))((c5$0 (c5$0$0 a2)) (c5$1) (c5$2) (c5$3 (c5$3$0 a0)) (c5$4) (c5$5 (c5$5$0 a4) (c5$5$1 Int)) (c5$6))((c6$0 (c6$0$0 a7) (c6$0$1 a7) (c6$0$2 String)) (c6$1) (c6$2) (c6$3) (c6$4) (c6$5) (c6$6))((c7$0 (c7$0$0 a2) (c7$0$1 Int)) (c7$1 (c7$1$0 a4) (c7$1$1 Int) (c7$1$2 Bool)))))
(define-funs-rec ((f0((v0 a6))a4))
                  (c4$2))
(check-sat)
