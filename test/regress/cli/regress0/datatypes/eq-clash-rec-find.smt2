; EXPECT: unsat
(set-logic ALL)
(declare-datatype Tree ((node (data Int) (left Tree) (right Tree)) (leaf)))
(declare-fun L () Tree)
(declare-fun x () Int)
(declare-fun y () Int)
; non-trivial instance of dt-cons-eq-clash reconstruction for nested values
(assert (= (node x (node y leaf leaf) (node y (node 5 leaf leaf) L))
           (node x (node 5 leaf L) (node 2 (node 3 leaf L) L))))
(check-sat)
