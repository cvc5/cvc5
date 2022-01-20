(set-logic ALL)

(set-info :status sat)

; forall c_cr:C. forall b_cq:B. A(c_cr & b_cq & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_cr () (Set Int))

(assert (set.subset c_cr UNIVERALSET))
(assert (>= (* 2 (set.card c_cr)) (+ (- n t) 1)))

(declare-fun b_cq () (Set Int))

(assert (set.subset b_cq UNIVERALSET))
(assert (>= (* 2 (set.card b_cq)) (+ (+ n (* 3 t)) 1)))


(assert
  (not
    (>= (set.card (set.inter (set.inter c_cr b_cq) (set.minus UNIVERALSET f))) (- n t))))

(check-sat)
