;(set-option :produce-models true)
(set-logic QF_ALL_SUPPORTED)
(set-info :status sat)
(declare-datatypes () (
  ( RealTree 
    ( Node 
      (left RealTree) 
		  (elem Real) 
		  (right RealTree)) 
    (Leaf)
   )
))

(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))

( declare-fun SumeAndPositiveTree ( RealTree ) (Pair Real Bool) )

(declare-fun l1 () RealTree)
(declare-fun l2 () RealTree)
(declare-const result (Pair Real Bool))
(assert (= l1 (Node l2 5.0 l2)))
(assert (= result (SumeAndPositiveTree l1)))
(assert (= (first result) 5))
(assert (= (second result) true))
(check-sat)
