;; Unary OR is not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(set-info :status unsat)
(declare-sort U 0)
(declare-datatypes ((T 0) (D 0)) (((E) (o (b Bool)) (I (t Int)) (i (v D)) (R (l T) (u T))) ((ic (vc U)))))
(declare-datatypes ((H 0)) (((M (h T)))))
(declare-fun S (U Int) T)
(declare-fun n () H)
(assert (and
(not (b (o (or (b (o (or (b (o (or (b (o (= (t (S (vc (v (S (vc (v E)) 0))) (t E))) (t (S (vc (v (S (vc (v (h n))) 0))) (t E))))))))))))))))
(b (o (forall ((i Int)) (or (< i (t (u (R E E)))) (b (o (forall ((z Int)) (! (or (b (o (or (b (o (< (t (S (vc (v (S (vc (v (h n))) z))) (t E))) (t (S (vc (v (S (vc (v (h n))) 0))) (t (I i))))))))))) :qid id))))))))))
(check-sat)
