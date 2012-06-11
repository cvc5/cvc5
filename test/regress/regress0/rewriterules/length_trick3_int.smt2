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

(declare-fun ten_one_cons (list) list)

(assert (forall ((?l list)) (! (= (ten_one_cons ?l)
        (cons 1 (cons 1 (cons 1 (cons 1 (cons 1 (cons 1 (cons 1 (cons 1 (cons 1 (cons 1 ?l) )))))))))
        ) :rewrite-rule)))

(assert (not (= (length (ten_one_cons nil))
        10)))

(check-sat)

(declare-fun ten_one_ten (list) list)

(assert (forall ((?l list)) (! (= (ten_one_ten ?l)
        (ten_one_cons (ten_one_cons (ten_one_cons (ten_one_cons (ten_one_cons (ten_one_cons (ten_one_cons (ten_one_cons (ten_one_cons (ten_one_cons ?l) )))))))))
        ) :rewrite-rule)))

(declare-fun two_one_ten (list) list)

(assert (forall ((?l list)) (! (= (two_one_ten ?l)
        (ten_one_cons (ten_one_cons ?l))
        ) :rewrite-rule)))

(exit)
