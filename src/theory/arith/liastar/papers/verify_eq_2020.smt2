(set-logic ALL)
(set-option :produce-models true)
(set-option :incremental true)
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
; (m,L,s)
; A1 = {(0, 0, 0)}, B1 = {(1, 1, 0), (0, 1, 1)}
; l1 = 0, l2 = 1
(assert 
 (= 
   SLS 
   (exists ((l1 Int) (l2 Int)) 
    (and (>= l1 0) (>= l2 0) 
         (= m l1) 
         (= L (+ l1 l2)) 
         (= s l2)))))

(push 1)
(assert (and F (not SLS)))
(check-sat)
(pop 1)
(push 1)
(assert (and (not F) SLS))
(check-sat)
(get-model)
(pop 1)