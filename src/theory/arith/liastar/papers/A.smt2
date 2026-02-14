
(set-logic ALL) 

(set-option :produce-models true) 

(declare-fun x1 () Int) 

(declare-fun L () Int) 

(declare-fun x () Int) 

(declare-fun z1 () Int) 

(declare-fun z2 () Int) 

(declare-fun A () Bool) 
(assert (>= x1 0)) 
(assert (>= L 0)) 
(assert (>= x 0)) 
(assert (>= z1 0)) 
(assert (>= z2 0)) 

(assert 
  (= A 
    (or 
      (and (<= L x) (= x1 0)) 
      (and (>= L (+ x 1)) (= x1 (- L x))) ) )) 

(assert 
  (distinct (not A) 
    (or 
      (and (>= L (+ x 1)) (<= L x)) 
      (and (>= x1 1) (<= L x)) 
      (and (>= L (+ x 1)) (>= x1 (+ (- L x) 1))) 
      (and (>= x1 1) (>= x1 (+ (- L x) 1))) 
      (and (>= L (+ x 1)) (<= x1 (- (- L x) 1))) 
      (and (>= x1 1) (<= x1 (- (- L x) 1))) ) ) ) 
(check-sat) 
(get-model)