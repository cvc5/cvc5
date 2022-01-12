; EXPECT: (>= (* (- 1.0) x) (- 100.0))
(set-logic LRA)  
(declare-fun x () Real)
(get-qe
 (exists ((Y Bool)) (>= (* (- 1.0) x) (- 100.0))
))
