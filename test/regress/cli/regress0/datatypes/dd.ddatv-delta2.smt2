; COMMAND-LINE: --preregister-mode=rlv
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-sort U 0)
(declare-datatypes ((T 0) (D 0)) (((E) (o (b Bool)) (I (t Int)) (i (v D))) ((i (v U)))))
(declare-datatypes ((H 0)) (((M (h T)))))
(declare-fun S (U Int) T)
(declare-fun n () H)
(assert (not (b (o (or (b (o (or (b (o (or (b (o (= (t (S (v (v (S (v (v E)) 0))) (t E))) (t (S (v (v (S (v (v (h n))) 0))) (t E)))))))))))))))))
(check-sat)
