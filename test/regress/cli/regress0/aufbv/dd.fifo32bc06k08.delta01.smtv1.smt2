; COMMAND-LINE: --bitwise-eq
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () (Array (_ BitVec 6) (_ BitVec 32)))
(check-sat-assuming ((not (= (_ bv0 1) (bvand (bvcomp (_ bv1 32) (select a (_ bv0 6))) (ite (= a (store a (_ bv0 6) (_ bv0 32))) (_ bv1 1) (_ bv0 1)))))))
