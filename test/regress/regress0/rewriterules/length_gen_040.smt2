;; Same than length.smt2 but the nil case is not a rewrite rule
;; So here the rewrite rules have no guards length

(set-logic AUFLIA)
(set-info :status unsat)

;; don't use a datatypes for currently focusing in uf
(declare-sort list 0)

(declare-fun cons (Int list) list)
(declare-fun nil  ()         list)


;;define length
(declare-fun length (list) Int)

(assert (= (length nil) 0))

(assert (forall ((?e Int) (?l list)) (! (= (length (cons ?e ?l)) (+ 1 (length ?l))) :rewrite-rule)))

(declare-fun gen_cons (Int list) list)

(assert (forall ((?n Int) (?l list)) (! (=> (= ?n 0) (= (gen_cons ?n ?l) ?l)) :rewrite-rule)))

(assert (forall ((?n Int) (?l list)) (! (=> (> ?n 0) (= (gen_cons ?n ?l)
        (gen_cons (- ?n 1) (cons 1 ?l)))) :rewrite-rule)))

(declare-fun n () Int)

(assert (not (= (length (gen_cons 40 nil)) 40)))

(check-sat)

(exit)
