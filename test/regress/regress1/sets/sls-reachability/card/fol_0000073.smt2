(set-logic ALL)

(set-info :status sat)

; forall c_cp:C. forall b_co:B. nonempty(c_cp & b_co & f & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_cp () (Set Int))

(assert (set.subset c_cp UNIVERALSET))
(assert (>= (* 2 (set.card c_cp)) (+ (- n t) 1)))

(declare-fun b_co () (Set Int))

(assert (set.subset b_co UNIVERALSET))
(assert (>= (* 2 (set.card b_co)) (+ (+ n (* 3 t)) 1)))


(assert
  (=
    (set.card
      (set.inter (set.inter (set.inter c_cp b_co) f) (set.minus UNIVERALSET f)))
    0))

(check-sat)
