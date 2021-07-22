; COMMAND-LINE: --decision=justification
; EXPECT: sat

(set-logic AUFLIRA)
(set-info :smt-lib-version 2.6)
(set-info :category "industrial")
(set-info :status sat)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (U) U)
(declare-fun p () Bool)
(assert (and (= a b) (forall ((x U)) (=> (and (= (f x) a) (not (= (f x) b))) p))))
(check-sat)
(exit)
