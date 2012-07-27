;; Same than length.smt2 but the nil case is not a rewrite rule
;; So here the rewrite rules have no guards length

(set-info :status unsat)

(declare-datatypes (
(nat  (succ (pred nat)) (zero ) )
(list  (cons (car nat)(cdr list)) (nil ) )

))


;;define length
(declare-fun length (list) nat)

(assert (= (length nil) zero))

(assert (forall ((?e nat) (?l list)) (! (= (length (cons ?e ?l)) (succ (length ?l))) :rewrite-rule)))

(declare-fun gen_cons (nat list) list)

(assert (forall ((?l list)) (! (= (gen_cons zero ?l) ?l) :rewrite-rule)))

(assert (forall ((?n nat) (?l list)) (! (= (gen_cons (succ ?n) ?l)
        (gen_cons ?n (cons zero ?l))) :rewrite-rule)))

(declare-fun n () nat)

(assert (not (= (length (gen_cons (succ (succ zero)) nil)) (succ (succ zero)))))

(check-sat)

(exit)
