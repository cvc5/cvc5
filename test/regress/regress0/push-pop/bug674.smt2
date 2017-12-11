; COMMAND-LINE: --quant-ind --incremental --rewrite-divk
(set-logic ALL_SUPPORTED)
(declare-datatypes ((Lst 0)) (((cons (head Int) (tail Lst)) (nil))))
(define-fun-rec app ((l1 Lst) (l2 Lst)) Lst (ite (is-nil l1) l2 (cons (head l1) (app (tail l1) l2))))
(define-fun-rec rev ((l Lst)) Lst (ite (is-nil l) nil (app (rev (tail l)) (cons (head l) nil))))
; EXPECT: unsat
(push 1)
(assert (not (=> true (and (forall (($l1$0 Lst) ($l2$0 Lst) ($l3$0 Lst)) (= (app $l1$0 (app $l2$0 $l3$0)) (app (app $l1$0 $l2$0) $l3$0)))))))
(check-sat)
(pop 1)

(assert (forall (($l1$0 Lst) ($l2$0 Lst) ($l3$0 Lst)) (= (app $l1$0 (app $l2$0 $l3$0)) (app (app $l1$0 $l2$0) $l3$0))))

; EXPECT: unsat
(push 1)
(assert (not (=> true (and (forall (($l1$0 Lst) ($l2$0 Lst)) (= (rev (app $l1$0 $l2$0)) (app (rev $l2$0) (rev $l1$0))))))))
(check-sat)
(pop 1)

(assert (forall (($l1$0 Lst) ($l2$0 Lst)) (= (rev (app $l1$0 $l2$0)) (app (rev $l2$0) (rev $l1$0)))))

; EXPECT: unsat
(push 1)
(assert (not (=> true (and (forall (($l1$0 Lst)) (= (rev (rev $l1$0)) $l1$0))))))
(check-sat)
(pop 1)


