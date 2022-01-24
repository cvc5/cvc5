(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall b_er:B. forall a_eq:A. 2b_er + 3a_eq + |UNIVERALSET| - 5n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_er () Int)

(assert (<= b_er n))
(assert (>= b_er 0))
(assert (>= (* 2 b_er) (+ (+ n (* 3 t)) 1)))

(declare-fun a_eq () Int)

(assert (<= a_eq n))
(assert (>= a_eq 0))
(assert (>= a_eq (- n t)))


(assert
 (and (< (- (+ (+ (* 2 b_er) (* 3 a_eq)) (bag.card UNIVERALSET)) (* 5 n)) 1) (> 1 0)))

(check-sat)
