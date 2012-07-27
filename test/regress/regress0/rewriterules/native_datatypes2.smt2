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

(assert-rewrite ((?e nat) (?l list)) () (length (cons ?e ?l)) (succ (length ?l)) () )
(assert-propagation ((?l list)) ((= (length ?l) zero)) () (= ?l nil) (((length ?l))) )
;(assert-propagation ((?l list)) () () (= ?l nil) (((= (length ?l) 0))) )

(declare-fun gen_cons (nat list) list)

(assert-rewrite ((?l list)) () (gen_cons zero ?l) ?l () )

(assert-rewrite ((?n nat) (?l list)) () (gen_cons (succ ?n) ?l) (gen_cons ?n (cons zero ?l)) () )

(declare-fun l1 () list)
(declare-fun l2 () list)

(assert (not (=> (= (length l1) zero) (= l1 nil))))

(check-sat)

(exit)
