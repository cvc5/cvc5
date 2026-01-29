
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
(echo "0")
(assert 
  (distinct
    (and (= z1 0) (= x1 (+ L (* (- 1) x))) (>= (+ L (* (- 1) x)) 1) (= z2 0) (>= (+ L (* (- 1) x)) 0))
    (exists ((l1 Int) (l2 Int)) (and (>= l1 0) (>= l2 0) (= x1 (+ 1 l2)) (= L (+ 1 l1 l2)) (= x l1) (= z1 0) (= z2 0)))
  )
)
(check-sat)
(pop 1)
(push 1)
(echo "1")
(assert 
  (distinct
    (and (= z1 0) (= x1 0) (< (+ L (* (- 1) x)) 1) (= z2 0) (>= (+ L (* (- 1) x)) 0))
    (exists ((l1 Int)) (and (>= l1 0) (= x1 0) (= L l1) (= x l1) (= z1 0) (= z2 0)))
  )
)
(check-sat)
(pop 1)
(push 1)
(echo "2")
(assert 
  (distinct
    (and (= z1 0) (= x1 0) (< (+ L (* (- 1) x)) 1) (= z2 1) (< (+ L (* (- 1) x)) 0))
    (exists ((l1 Int) (l2 Int)) (and (>= l1 0) (>= l2 0) (= x1 0) (= L l2) (= x (+ 1 l1 l2)) (= z1 0) (= z2 1)))
  )
)
(check-sat)
(pop 1)
(push 1)
(echo "3")
(assert 
  (distinct
    (and (= z1 1) (>= (+ x1 (* (- 1) L) x) 1) (>= x1 1) (= z2 0) (>= (+ L (* (- 1) x)) 0))
    (exists ((l1 Int) (l2 Int) (l3 Int)) (and (>= l1 0) (>= l2 0) (>= l3 0) (= x1 (+ 1 l2 l3)) (= L (+ l1 l3)) (= x l1) (= z1 1) (= z2 0)))
  )
)
(check-sat)
(pop 1)
(push 1)
(echo "4")
(assert 
  (distinct
    (and (= z1 1) (>= (+ x1 (* (- 1) L) x) 1) (>= x1 1) (= z2 1) (< (+ L (* (- 1) x)) 0))
    (exists ((l1 Int) (l2 Int) (l3 Int)) (and (>= l1 0) (>= l2 0) (>= l3 0) (= x1 (+ 1 l3)) (= L l2) (= x (+ 1 l1 l2)) (= z1 1) (= z2 1)))
  )
)
(check-sat)
(pop 1)
(push 1)
(echo "5")
(assert 
  (distinct
    (and (= z1 1) (>= (+ x1 (* (- 1) L) x) 1) (>= (+ L (* (- 1) x)) 1) (= z2 0) (>= (+ L (* (- 1) x)) 0))
    (exists ((l1 Int) (l2 Int) (l3 Int)) (and (>= l1 0) (>= l2 0) (>= l3 0) (= x1 (+ 2 l2 l3)) (= L (+ 1 l1 l3)) (= x l1) (= z1 1) (= z2 0)))
  )
)
(check-sat)
(pop 1)
(push 1)
(echo "6")
(assert 
  (distinct
    (and (= z1 1) (< (+ x1 (* (- 1) L) x) 0) (>= x1 1) (= z2 0) (>= (+ L (* (- 1) x)) 0))
    (exists ((l1 Int) (l2 Int) (l3 Int)) (and (>= l1 0) (>= l2 0) (>= l3 0) (= x1 (+ 1 l3)) (= L (+ 2 l1 l2 l3)) (= x l2) (= z1 1) (= z2 0)))
  )
)
(check-sat)
(pop 1)
(push 1)
(echo "7")
(assert 
  (distinct
    (and (= z1 1) (< (+ x1 (* (- 1) L) x) 0) (>= (+ L (* (- 1) x)) 1) (= z2 0) (>= (+ L (* (- 1) x)) 0))
    (exists ((l1 Int) (l2 Int) (l3 Int)) (and (>= l1 0) (>= l2 0) (>= l3 0) (= x1 l3) (= L (+ 1 l1 l2 l3)) (= x l2) (= z1 1) (= z2 0)))
  )
)
(check-sat)
(pop 1)
(push 1)
(echo "8")
(assert 
  (distinct
    (and (= z1 1) (< (+ L (* (- 1) x)) 1) (>= x1 1) (= z2 0) (>= (+ L (* (- 1) x)) 0))
    (exists ((l1 Int) (l2 Int)) (and (>= l1 0) (>= l2 0) (= x1 (+ 1 l2)) (= L l1) (= x l1) (= z1 1) (= z2 0)))
  )
)
(check-sat)
(pop 1)
(push 1)
(echo "9")
(assert 
  (distinct
    (and (= z1 1) (< (+ L (* (- 1) x)) 1) (>= x1 1) (= z2 1) (< (+ L (* (- 1) x)) 0))
    (exists ((l1 Int) (l2 Int) (l3 Int)) (and (>= l1 0) (>= l2 0) (>= l3 0) (= x1 (+ 1 l3)) (= L l2) (= x (+ 1 l1 l2)) (= z1 1) (= z2 1)))
  )
)
(check-sat)
(pop 1)
