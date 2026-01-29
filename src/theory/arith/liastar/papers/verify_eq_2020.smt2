(set-logic ALL)
(set-option :produce-models true)
(set-option :dag-thresh 0)
;------------------------
(declare-fun m () Int)
(declare-fun L () Int)
(declare-fun s () Int)
;------------------------
(declare-fun F () Bool)
(declare-fun SLS () Bool)

(assert (>= m 0))
(assert (>= L 0))
(assert (>= s 0))

(assert (= F (and (= m (- L s)) (<= s m))))
; l1 = 0, l2 = 1
(assert (= SLS (exists ((l1 Int) (l2 Int)) 
      (and 
        (>= l1 0) 
        (>= l2 0) 
        (= m l1) 
        (= L (+ l1 l2)) 
        (= s l2)))))
;(assert (and F (not SLS)))
(assert (and (not F) SLS))
(check-sat)
(get-model)