(set-logic ALL)

(set-info :status sat)

; forall b_et:B. forall b_es:B. forall b_er:B. forall a_eq:A. forall a_ep:A. nonempty(b_et & b_es & b_er & a_eq & a_ep & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_et () (Set Int))

(assert (set.subset b_et UNIVERALSET))
(assert (>= (* 2 (set.card b_et)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_es () (Set Int))

(assert (set.subset b_es UNIVERALSET))
(assert (>= (* 2 (set.card b_es)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_er () (Set Int))

(assert (set.subset b_er UNIVERALSET))
(assert (>= (* 2 (set.card b_er)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_eq () (Set Int))

(assert (set.subset a_eq UNIVERALSET))
(assert (>= (set.card a_eq) (- n t)))

(declare-fun a_ep () (Set Int))

(assert (set.subset a_ep UNIVERALSET))
(assert (>= (set.card a_ep) (- n t)))


(assert
  (=
    (set.card
      (set.inter
        (set.inter (set.inter (set.inter (set.inter b_et b_es) b_er) a_eq) a_ep)
        (set.minus UNIVERALSET f)))
    0))

(check-sat)
