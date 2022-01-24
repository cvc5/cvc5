(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_bd:B. forall a_bc:A. b_bd + a_bc + |f & ~f| - 2n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_bd () Int)

(assert (<= b_bd n))
(assert (>= b_bd 0))
(assert (>= (* 2 b_bd) (+ (+ n (* 3 t)) 1)))

(declare-fun a_bc () Int)

(assert (<= a_bc n))
(assert (>= a_bc 0))
(assert (>= a_bc (- n t)))


(assert
 (and
  (<
   (* 2
      (-
       (+ (+ b_bd a_bc)
          (bag.card (bag.inter_min f (bag.difference_subtract UNIVERALSET f))))
       (* 2 n)))
   (+ (- n t) 1))
  (> (+ (- n t) 1) (* 2 0))))

(check-sat)
