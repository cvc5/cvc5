(set-logic ALL)

(set-info :status sat)

; forall c_fo:C. forall b_fn:B. forall a_fm:A. forall a_fl:A. nonempty(c_fo & b_fn & a_fm & a_fl & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_fo () (Set Int))

(assert (set.subset c_fo UNIVERALSET))
(assert (>= (* 2 (set.card c_fo)) (+ (- n t) 1)))

(declare-fun b_fn () (Set Int))

(assert (set.subset b_fn UNIVERALSET))
(assert (>= (* 2 (set.card b_fn)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_fm () (Set Int))

(assert (set.subset a_fm UNIVERALSET))
(assert (>= (set.card a_fm) (- n t)))

(declare-fun a_fl () (Set Int))

(assert (set.subset a_fl UNIVERALSET))
(assert (>= (set.card a_fl) (- n t)))


(assert
  (=
    (set.card
      (set.inter (set.inter (set.inter (set.inter c_fo b_fn) a_fm) a_fl)
                    (set.minus UNIVERALSET f)))
    0))

(check-sat)
