; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-option :produce-models true)
(set-logic ALL)
(declare-datatypes ((a0 0)(a1 0)(a2 0)(a3 0)(a4 0)(a5 0)(a6 0)(a7 0)(a8 0)(a9 0)(aa 0)(ab 0)) (((c0$0) (c0$1) (c0$2) (c0$3 (c0$3$0 a8) (c0$3$1 Int)) (c0$4 (c0$4$0 a5) (c0$4$1 a6)) (c0$5) (c0$6) (c0$7) (c0$8))((c1$0) (c1$1 (c1$1$0 a4) (c1$1$1 Bool) (c1$1$2 a6) (c1$1$3 a4) (c1$1$4 ab) (c1$1$5 Int) (c1$1$6 a0)) (c1$2) (c1$3) (c1$4) (c1$5 (c1$5$0 a7)) (c1$6 (c1$6$0 String) (c1$6$1 a4) (c1$6$2 a4) (c1$6$3 a0)) (c1$7))((c2$0) (c2$1 (c2$1$0 aa) (c2$1$1 aa) (c2$1$2 a1) (c2$1$3 a0) (c2$1$4 a0) (c2$1$5 a0) (c2$1$6 a9)) (c2$2 (c2$2$0 a5) (c2$2$1 ab)) (c2$3 (c2$3$0 Bool) (c2$3$1 a7) (c2$3$2 a3) (c2$3$3 Bool) (c2$3$4 a0) (c2$3$5 String)) (c2$4))((c3$0 (c3$0$0 a7)) (c3$1) (c3$2) (c3$3) (c3$4) (c3$5) (c3$6) (c3$7) (c3$8) (c3$9) (c3$a) (c3$b) (c3$c))((c4$0 (c4$0$0 a2) (c4$0$1 a1) (c4$0$2 Bool) (c4$0$3 String) (c4$0$4 a3) (c4$0$5 Int) (c4$0$6 a2)))((c5$0) (c5$1) (c5$2 (c5$2$0 String)) (c5$3) (c5$4) (c5$5) (c5$6 (c5$6$0 a0) (c5$6$1 a6) (c5$6$2 a3) (c5$6$3 a3) (c5$6$4 a9)) (c5$7))((c6$0) (c6$1 (c6$1$0 a7)) (c6$2) (c6$3) (c6$4 (c6$4$0 a7) (c6$4$1 a3) (c6$4$2 a4)) (c6$5 (c6$5$0 a9) (c6$5$1 a9) (c6$5$2 a7) (c6$5$3 a6) (c6$5$4 ab) (c6$5$5 a5) (c6$5$6 a3) (c6$5$7 aa)) (c6$6) (c6$7) (c6$8) (c6$9) (c6$a) (c6$b) (c6$c))((c7$0) (c7$1) (c7$2) (c7$3 (c7$3$0 a8) (c7$3$1 Bool) (c7$3$2 Int) (c7$3$3 a5) (c7$3$4 a8)) (c7$4) (c7$5) (c7$6) (c7$7) (c7$8 (c7$8$0 a5) (c7$8$1 a1)))((c8$0 (c8$0$0 a6) (c8$0$1 ab) (c8$0$2 ab) (c8$0$3 a1) (c8$0$4 Bool)) (c8$1 (c8$1$0 a4) (c8$1$1 Bool) (c8$1$2 a2) (c8$1$3 String) (c8$1$4 Bool)))((c9$0 (c9$0$0 String)) (c9$1 (c9$1$0 String) (c9$1$1 ab)) (c9$2 (c9$2$0 a5) (c9$2$1 a9)) (c9$3 (c9$3$0 String) (c9$3$1 a8) (c9$3$2 a6)) (c9$4) (c9$5))((ca$0 (ca$0$0 String) (ca$0$1 a3) (ca$0$2 a9) (ca$0$3 a3) (ca$0$4 Bool) (ca$0$5 a1) (ca$0$6 a1) (ca$0$7 a4)) (ca$1) (ca$2 (ca$2$0 a4) (ca$2$1 String) (ca$2$2 aa) (ca$2$3 ab)))((cb$0 (cb$0$0 a5) (cb$0$1 a2) (cb$0$2 a3) (cb$0$3 aa) (cb$0$4 Bool)) (cb$1 (cb$1$0 a0)) (cb$2) (cb$3) (cb$4) (cb$5) (cb$6) (cb$7 (cb$7$0 String) (cb$7$1 a0) (cb$7$2 a7) (cb$7$3 ab) (cb$7$4 aa) (cb$7$5 a8)) (cb$8))))
(push 1)
(declare-fun v0() a0)
(push 1)
(assert (is-c0$0 v0))
(check-sat)
(pop 1)
(push 1)
(assert (is-c0$1 v0))
(check-sat)
(pop 1)
(push 1)
(assert (is-c0$2 v0))
(check-sat)
(pop 1)
(push 1)
(assert (is-c0$3 v0))
(check-sat)
(pop 1)
(push 1)
(assert (is-c0$4 v0))
(check-sat)
(pop 1)
(push 1)
(assert (is-c0$5 v0))
(check-sat)

