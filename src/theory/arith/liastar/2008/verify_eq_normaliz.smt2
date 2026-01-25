(set-logic ALL)
(set-option :produce-models true)
(set-option :dag-thresh 0)
;------------------------
(declare-fun x1 () Int)
(declare-fun L () Int)
(declare-fun x () Int)
(declare-fun z1 () Int)
(declare-fun z2 () Int)
;------------------------
(declare-fun F () Bool)
(declare-fun SLS () Bool)

(assert (>= x1 0))
(assert (>= L 0))
(assert (>= x 0))
(assert (>= z1 0))
(assert (>= z2 0))

(assert 
 (= F 
   (and 
     (= z1 (ite (= x1 (ite (<= L x) 0 (- L x))) 0 1))
     (= z2 (ite (<= x L) 0 1))
   )
 )
)

; (x1,L,x, z1, z2)
; A1 = {(0, 0, 0, 0, 0)}, B1 = {(0, 1, 1, 0, 0)}
; A2 = {(1, 0, 0, 1, 0)}, B2 = {(0, 1, 1, 0, 0), (1, 0, 0, 0, 0)}
; A3 = {(0, 0, 1, 0, 1)}, B3 = {(0, 1, 1, 0, 0), (0, 0, 1, 0, 0)}
; A4 = {(1, 0, 1, 1, 1)}, B4 = {(0, 1, 1, 0, 0), (0, 0, 1, 0, 0)}
; A5 = {(1, 1, 0, 0, 0)}, B5 = {(1, 1, 0, 0, 0), (0, 1, 1, 0, 0)}
; A6 = {(2, 1, 0, 1, 0)}, B6 = {(1, 1, 0, 0, 0), (0, 1, 1, 0, 0), (1, 0, 0, 0, 0)}
; A7 = {(0, 0, 1, 1, 0)}, B7 = {(1, 1, 0, 0, 0), (0, 1, 0, 0, 0), (0, 0, 1, 1, 0)}
(assert 
 (= 
  SLS 
  (or   
    (exists ((l1 Int) (l2 Int)) (and (>= l1 0) (>= l2 0) (= x1 (+ 1 l2)) (= L (+ 1 l1 l2)) (= x l1) (= z1 0) (= z2 0)))
    (exists ((l1 Int)) (and (>= l1 0) (= x1 0) (= L l1) (= x l1) (= z1 0) (= z2 0)))
    (exists ((l1 Int)) (and (>= l1 0) (= x1 0) (= L l1) (= x l1) (= z1 0) (= z2 0)))
    (exists ((l1 Int) (l2 Int)) (and (>= l1 0) (>= l2 0) (= x1 0) (= L l2) (= x (+ 1 l1 l2)) (= z1 0) (= z2 1)))
    (exists ((l1 Int) (l2 Int) (l3 Int)) (and (>= l1 0) (>= l2 0) (>= l3 0) (= x1 (+ 1 l2 l3)) (= L (+ l1 l3)) (= x l1) (= z1 1) (= z2 0)))
    (exists ((l1 Int) (l2 Int) (l3 Int)) (and (>= l1 0) (>= l2 0) (>= l3 0) (= x1 (+ 1 l3)) (= L l2) (= x (+ 1 l1 l2)) (= z1 1) (= z2 1)))
    (exists ((l1 Int)) (and (>= l1 0) (= x1 0) (= L l1) (= x l1) (= z1 0) (= z2 0)))
    (exists ((l1 Int) (l2 Int)) (and (>= l1 0) (>= l2 0) (= x1 0) (= L l2) (= x (+ l1 l2)) (= z1 0) (= z2 0)))
    (exists ((l1 Int) (l2 Int) (l3 Int)) (and (>= l1 0) (>= l2 0) (>= l3 0) (= x1 (+ 2 l2 l3)) (= L (+ 1 l1 l3)) (= x l1) (= z1 1) (= z2 0)))
    (exists ((l1 Int) (l2 Int)) (and (>= l1 0) (>= l2 0) (= x1 l2) (= L l1) (= x l1) (= z1 0) (= z2 0)))
    (exists ((l1 Int) (l2 Int) (l3 Int)) (and (>= l1 0) (>= l2 0) (>= l3 0) (= x1 (+ 1 l3)) (= L (+ 2 l1 l2 l3)) (= x l2) (= z1 1) (= z2 0)))
    (exists ((l1 Int)) (and (>= l1 0) (= x1 0) (= L l1) (= x l1) (= z1 0) (= z2 0)))
    (exists ((l1 Int) (l2 Int)) (and (>= l1 0) (>= l2 0) (= x1 0) (= L (+ l1 l2)) (= x l2) (= z1 0) (= z2 0)))
    (exists ((l1 Int)) (and (>= l1 0) (= x1 0) (= L l1) (= x l1) (= z1 0) (= z2 0)))
    (exists ((l1 Int) (l2 Int) (l3 Int)) (and (>= l1 0) (>= l2 0) (>= l3 0) (= x1 l3) (= L (+ 1 l1 l2 l3)) (= x l2) (= z1 1) (= z2 0)))
    (exists ((l1 Int)) (and (>= l1 0) (= x1 0) (= L l1) (= x l1) (= z1 0) (= z2 0)))
    (exists ((l1 Int) (l2 Int)) (and (>= l1 0) (>= l2 0) (= x1 (+ 1 l2)) (= L l1) (= x l1) (= z1 1) (= z2 0)))
    (exists ((l1 Int) (l2 Int) (l3 Int)) (and (>= l1 0) (>= l2 0) (>= l3 0) (= x1 (+ 1 l3)) (= L l2) (= x (+ 1 l1 l2)) (= z1 1) (= z2 1)))
    (exists ((l1 Int)) (and (>= l1 0) (= x1 0) (= L l1) (= x l1) (= z1 0) (= z2 0)))
    (exists ((l1 Int) (l2 Int)) (and (>= l1 0) (>= l2 0) (= x1 0) (= L l2) (= x (+ l1 l2)) (= z1 0) (= z2 0)))
    (exists ((l1 Int) (l2 Int)) (and (>= l1 0) (>= l2 0) (= x1 l2) (= L l1) (= x l1) (= z1 0) (= z2 0)))
    (exists ((l1 Int) (l2 Int)) (and (>= l1 0) (>= l2 0) (= x1 l2) (= L l1) (= x l1) (= z1 0) (= z2 0)))

  )
 )
)

(assert (and F (not SLS)))
(check-sat)
(get-model)
