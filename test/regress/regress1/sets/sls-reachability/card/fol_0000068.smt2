(set-logic ALL)

(set-info :status unsat)

; forall c_cd:C. nonempty(c_cd & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_cd () (Set Int))

(assert (set.subset c_cd UNIVERALSET))
(assert (>= (* 2 (set.card c_cd)) (+ (- n t) 1)))


(assert (= (set.card (set.inter c_cd (set.minus UNIVERALSET f))) 0))

(check-sat)
