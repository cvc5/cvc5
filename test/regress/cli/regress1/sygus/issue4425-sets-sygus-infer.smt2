; COMMAND-LINE: --sygus-inference -q
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic ALL)
(declare-fun a () Int)
(declare-fun d () Int)
(declare-fun f () Int)
(declare-fun b () (Set Int))
(declare-fun c () (Set Int))
(declare-fun e () (Set Int))
(assert (> a (mod d f) (set.card (set.minus e (set.minus (set.minus e b) (set.inter e c)))) a))
(check-sat)
