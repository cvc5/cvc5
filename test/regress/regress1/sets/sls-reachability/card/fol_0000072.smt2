(set-logic ALL)

(set-info :status sat)

; forall c_cn:C. forall c_cm:C. forall b_cl:B. nonempty(c_cn & c_cm & b_cl & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_cn () (Set Int))

(assert (set.subset c_cn UNIVERALSET))
(assert (>= (* 2 (set.card c_cn)) (+ (- n t) 1)))

(declare-fun c_cm () (Set Int))

(assert (set.subset c_cm UNIVERALSET))
(assert (>= (* 2 (set.card c_cm)) (+ (- n t) 1)))

(declare-fun b_cl () (Set Int))

(assert (set.subset b_cl UNIVERALSET))
(assert (>= (* 2 (set.card b_cl)) (+ (+ n (* 3 t)) 1)))


(assert
  (=
    (set.card
      (set.inter (set.inter (set.inter c_cn c_cm) b_cl) (set.minus UNIVERALSET f)))
    0))

(check-sat)
