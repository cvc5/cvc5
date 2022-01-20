(set-logic ALL)

(set-info :status unsat)

; forall c_dn:C. nonempty(c_dn & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_dn () (Set Int))

(assert (set.subset c_dn UNIVERALSET))
(assert (>= (* 2 (set.card c_dn)) (+ (- n t) 1)))


(assert (= (set.card (set.inter c_dn (set.minus UNIVERALSET f))) 0))

(check-sat)
