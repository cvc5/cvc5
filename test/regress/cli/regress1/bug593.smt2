(set-logic QF_UFBV)
(set-info :status unsat)

(declare-sort A 0)

(declare-fun f ((_ BitVec 1)) A)
(declare-fun g (A) (_ BitVec 1))

(declare-fun x () A)
(declare-fun y () A)
(declare-fun z () A)
 
(assert (and
 
(not (= (f (g x)) (f (g y))))
(not (= (f (g x)) (f (g z))))
(not (= (f (g y)) (f (g z))))))
  
(check-sat)

