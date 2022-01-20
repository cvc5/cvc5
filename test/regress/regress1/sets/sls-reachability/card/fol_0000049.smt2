(set-logic ALL)

(set-info :status sat)

; forall c_bd:C. forall b_bc:B. forall a_bb:A. C(c_bd & b_bc & a_bb & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_bd () (Set Int))

(assert (set.subset c_bd UNIVERALSET))
(assert (>= (* 2 (set.card c_bd)) (+ (- n t) 1)))

(declare-fun b_bc () (Set Int))

(assert (set.subset b_bc UNIVERALSET))
(assert (>= (* 2 (set.card b_bc)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_bb () (Set Int))

(assert (set.subset a_bb UNIVERALSET))
(assert (>= (set.card a_bb) (- n t)))


(assert
  (not
    (>=
      (* 2
         (set.card
           (set.inter (set.inter (set.inter c_bd b_bc) a_bb) (set.minus UNIVERALSET f))))
      (+ (- n t) 1))))

(check-sat)
