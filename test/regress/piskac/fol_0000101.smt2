(set-logic ALL)
(set-info :status unsat)

; forall b_ed:B. forall a_ec:A. 2b_ed + 2a_ec + |f & ~f| - 4n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_ed () Int)
(assert (<= b_ed n))
(assert (>= b_ed 0))
(assert (>= (* 2 b_ed) (+ (+ n (* 3 t)) 1)))

(declare-fun a_ec () Int)
(assert (<= a_ec n))
(assert (>= a_ec 0))
(assert (>= a_ec (- n t)))


(assert (and (< (- (+ (+ (* 2 b_ed) (* 2 a_ec)) (set.card (set.inter f (set.minus UNIVERALSET f)))) (* 4 n)) 1) (> 1 0)))

(check-sat)
