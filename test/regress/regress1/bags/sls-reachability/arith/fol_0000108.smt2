(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_et:B. forall a_es:A. 2b_et + 3a_es + |UNIVERALSET| - 5n >= n or n <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_et () Int)

(assert (<= b_et n))
(assert (>= b_et 0))
(assert (>= (* 2 b_et) (+ (+ n (* 3 t)) 1)))

(declare-fun a_es () Int)

(assert (<= a_es n))
(assert (>= a_es 0))
(assert (>= a_es (- n t)))


(assert
 (and (< (- (+ (+ (* 2 b_et) (* 3 a_es)) (bag.card UNIVERALSET)) (* 5 n)) n) (> n 0)))

(check-sat)
