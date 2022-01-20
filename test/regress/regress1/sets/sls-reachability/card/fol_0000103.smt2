(set-logic ALL)

(set-info :status sat)

; forall b_fk:B. forall b_fj:B. forall a_fi:A. forall a_fh:A. A(b_fk & b_fj & a_fi & a_fh & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_fk () (Set Int))

(assert (set.subset b_fk UNIVERALSET))
(assert (>= (* 2 (set.card b_fk)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_fj () (Set Int))

(assert (set.subset b_fj UNIVERALSET))
(assert (>= (* 2 (set.card b_fj)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_fi () (Set Int))

(assert (set.subset a_fi UNIVERALSET))
(assert (>= (set.card a_fi) (- n t)))

(declare-fun a_fh () (Set Int))

(assert (set.subset a_fh UNIVERALSET))
(assert (>= (set.card a_fh) (- n t)))


(assert
  (not
    (>=
      (set.card
        (set.inter (set.inter (set.inter (set.inter b_fk b_fj) a_fi) a_fh)
                      (set.minus UNIVERALSET f)))
      (- n t))))

(check-sat)
