(set-logic ALL)

(set-info :status sat)

; forall c_fg:C. forall b_ff:B. forall b_fe:B. forall a_fd:A. nonempty(c_fg & b_ff & b_fe & a_fd & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_fg () (Set Int))

(assert (set.subset c_fg UNIVERALSET))
(assert (>= (* 2 (set.card c_fg)) (+ (- n t) 1)))

(declare-fun b_ff () (Set Int))

(assert (set.subset b_ff UNIVERALSET))
(assert (>= (* 2 (set.card b_ff)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_fe () (Set Int))

(assert (set.subset b_fe UNIVERALSET))
(assert (>= (* 2 (set.card b_fe)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_fd () (Set Int))

(assert (set.subset a_fd UNIVERALSET))
(assert (>= (set.card a_fd) (- n t)))


(assert
  (=
    (set.card
      (set.inter (set.inter (set.inter (set.inter c_fg b_ff) b_fe) a_fd)
                    (set.minus UNIVERALSET f)))
    0))

(check-sat)
