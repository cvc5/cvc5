;; Same than length.smt2 but the nil case is not a rewrite rule
;; So here the rewrite rules have no guards length

(set-logic AUFLIA)
(set-info :status unsat)

;; don't use a datatypes for currently focusing in uf
(declare-sort list 0)
;; don't use arith
(declare-sort mynat 0)
(declare-fun zero () mynat)
(declare-fun succ (mynat) mynat)

(declare-fun cons (Int list) list)
(declare-fun nil  ()         list)
(declare-fun p (list) Bool)


;;define length
(declare-fun length (list) mynat)

(assert (= (length nil) zero))

(assert (forall ((?e Int) (?l list)) (! (= (length (cons ?e ?l)) (succ (length ?l))) :rewrite-rule)))

(declare-fun ten_one_cons (list) list)

(assert (forall ((?l list)) (! (=> (p ?l) (= (ten_one_cons ?l)
        (cons 1 (cons 1 (cons 1 (cons 1 (cons 1 (cons 1 (cons 1 (cons 1 (cons 1 (cons 1 ?l) )))))))))
        )) :rewrite-rule)))

(declare-fun a  () Bool)
(declare-fun b  () Bool)
(declare-fun c  () Bool)

(assert (=> a (p nil)) )
(assert (=> b (p nil)) )
(assert (or a b))

(assert (not (= (length (ten_one_cons nil))
        (succ(succ(succ(succ(succ(succ(succ(succ(succ(succ zero)))))))))))))

(check-sat)

(exit)
