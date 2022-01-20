(set-logic ALL)

(set-info :status sat)

; forall c_cx:C. forall b_cw:B. C(c_cx & b_cw & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_cx () (Set Int))

(assert (set.subset c_cx UNIVERALSET))
(assert (>= (* 2 (set.card c_cx)) (+ (- n t) 1)))

(declare-fun b_cw () (Set Int))

(assert (set.subset b_cw UNIVERALSET))
(assert (>= (* 2 (set.card b_cw)) (+ (+ n (* 3 t)) 1)))


(assert
  (not
    (>=
      (* 2 (set.card (set.inter (set.inter c_cx b_cw) (set.minus UNIVERALSET f))))
      (+ (- n t) 1))))

(check-sat)
