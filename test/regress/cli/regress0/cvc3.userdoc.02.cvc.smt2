; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () (_ BitVec 5))
(declare-fun y () (_ BitVec 4))
(declare-fun yy () (_ BitVec 3))
(check-sat-assuming ( (not (= ((_ extract 8 4) (bvadd (concat x #b0000) (concat (concat #b000 (bvnot y)) #b11))) (bvadd x ((_ zero_extend 3) (bvnot ((_ extract 3 2) y)))))) ))
