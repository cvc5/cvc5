(set-logic ALL)

(set-info :status unsat)

; forall c_cc:C. nonempty(c_cc & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_cc () (Set Int))

(assert (set.subset c_cc UNIVERALSET))
(assert (>= (* 2 (set.card c_cc)) (+ (- n t) 1)))


(assert (= (set.card (set.inter c_cc (set.minus UNIVERALSET f))) 0))

(check-sat)
