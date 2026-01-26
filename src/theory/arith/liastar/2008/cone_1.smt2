
(set-logic ALL) 

(set-option :produce-models true) 

(set-option :incremental true) 

(set-option :dag-thresh 0) 

(declare-fun x1 () Int) 

(declare-fun L () Int) 

(declare-fun x () Int) 

(declare-fun z1 () Int) 

(declare-fun z2 () Int) 

(declare-fun predicate () Bool) 

(declare-fun dnf () Bool) 
(assert (>= x1 0)) 
(assert (>= L 0)) 
(assert (>= x 0)) 
(assert (>= z1 0)) 
(assert (>= z2 0)) 
(push 1) 
(echo "1") 

(assert  
    (and 
      (= z1 0) 
      (= x1 (+ L (* (- 1) x))) 
      (>= (+ L (* (- 1) x)) 1) 
      (= z2 1) 
      (< (+ L (* (- 1) x)) 0)) 
    ) 

;; (assert 
;;   (distinct 
;;     (and 
;;       (= z1 0) 
;;       (= x1 (+ L (* (- 1) x))) 
;;       (>= (+ L (* (- 1) x)) 1) 
;;       (= z2 1) 
;;       (< (+ L (* (- 1) x)) 0)) 
;;     (exists ((l1 Int)) 
;;       (and (>= l1 0) (= x1 0) (= L l1) (= x l1) (= z1 0) (= z2 0))) ) ) 
(check-sat) 
(get-model)
(pop 1) 
