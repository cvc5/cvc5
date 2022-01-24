(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_fk:B. forall b_fj:B. forall a_fi:A. forall a_fh:A. A(b_fk & b_fj & a_fi & a_fh & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_fk () (Bag Int))

(assert (bag.subbag b_fk UNIVERALSET))
(assert (>= (* 2 (bag.card b_fk)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_fj () (Bag Int))

(assert (bag.subbag b_fj UNIVERALSET))
(assert (>= (* 2 (bag.card b_fj)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_fi () (Bag Int))

(assert (bag.subbag a_fi UNIVERALSET))
(assert (>= (bag.card a_fi) (- n t)))

(declare-fun a_fh () (Bag Int))

(assert (bag.subbag a_fh UNIVERALSET))
(assert (>= (bag.card a_fh) (- n t)))


(assert
 (not
  (>=
   (bag.card
    (bag.inter_min
     (bag.inter_min (bag.inter_min (bag.inter_min b_fk b_fj) a_fi) a_fh)
     (bag.difference_subtract UNIVERALSET f)))
   (- n t))))

(check-sat)
