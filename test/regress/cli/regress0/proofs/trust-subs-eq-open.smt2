(set-logic ALL)
(set-info :status unsat)
(declare-fun c () (_ BitVec 3))
(check-sat-assuming (
(and 
(= (_ bv0 1) ((_ extract 1 1) c)) 
(= (_ bv1 1) ((_ extract 0 0) c)) 
(not (= (_ bv1 2) ((_ extract 1 0) c))))))
