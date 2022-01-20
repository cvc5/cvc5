(set-logic ALL)

(set-info :status unsat)

; forall b_eo:B. forall b_en:B. forall a_em:A. forall a_el:A. nonempty(b_eo & b_en & a_em & a_el & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_eo () (Set Int))

(assert (set.subset b_eo UNIVERALSET))
(assert (>= (* 2 (set.card b_eo)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_en () (Set Int))

(assert (set.subset b_en UNIVERALSET))
(assert (>= (* 2 (set.card b_en)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_em () (Set Int))

(assert (set.subset a_em UNIVERALSET))
(assert (>= (set.card a_em) (- n t)))

(declare-fun a_el () (Set Int))

(assert (set.subset a_el UNIVERALSET))
(assert (>= (set.card a_el) (- n t)))


(assert
  (=
    (set.card
      (set.inter (set.inter (set.inter (set.inter b_eo b_en) a_em) a_el)
                    (set.minus UNIVERALSET f)))
    0))

(check-sat)
