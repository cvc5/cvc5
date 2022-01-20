(set-logic ALL)

(set-info :status unsat)

; forall c_ec:C. nonempty(c_ec & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_ec () (Set Int))

(assert (set.subset c_ec UNIVERALSET))
(assert (>= (* 2 (set.card c_ec)) (+ (- n t) 1)))


(assert (= (set.card (set.inter c_ec (set.minus UNIVERALSET f))) 0))

(check-sat)
