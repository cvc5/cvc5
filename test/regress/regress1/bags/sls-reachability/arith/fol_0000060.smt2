(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall a_bs:A. a_bs + |~f| - n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_bs () Int)

(assert (<= a_bs n))
(assert (>= a_bs 0))
(assert (>= a_bs (- n t)))


(assert
 (and
  (< (* 2 (- (+ a_bs (bag.card (bag.difference_subtract UNIVERALSET f))) n))
     (+ (- n t) 1))
  (> (+ (- n t) 1) (* 2 0))))

(check-sat)
