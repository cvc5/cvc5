(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_bl:C. forall a_bk:A. c_bl + a_bk + |~f| - 2n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_bl () Int)

(assert (<= c_bl n))
(assert (>= c_bl 0))
(assert (>= (* 2 c_bl) (+ (- n t) 1)))

(declare-fun a_bk () Int)

(assert (<= a_bk n))
(assert (>= a_bk 0))
(assert (>= a_bk (- n t)))


(assert
 (and
  (<
   (* 2
      (- (+ (+ c_bl a_bk) (bag.card (bag.difference_subtract UNIVERALSET f))) (* 2 n)))
   (+ (- n t) 1))
  (> (+ (- n t) 1) (* 2 0))))

(check-sat)
