; EXPECT: unsat
(set-logic ALL)
(declare-const x238 Bool)
(declare-const x24 Bool)
(declare-const x2 Bool)
(declare-const x23 Bool)
(declare-const x Bool)
(declare-const x7 Bool)
(declare-const x37 Bool)
(declare-const x3 Bool)
(declare-const x9 Bool)
(declare-const x8 Bool)
(declare-const x814 Bool)
(declare-const x81 Bool)
(declare-const x815 Bool)
(declare-const x82 Bool)
(assert (forall ((r Bool) (ri Bool) (Ve Bool) (e (_ BitVec 6)) (i Bool) (f Bool)) (exists ((er (_ BitVec 6)) (V Bool)) 
(or 
f 
(and x37 x81 x23 x3 x8 x x815 x24 x238 ri x7 x2 x814 x82 (not (ite x82 false Ve))) 
(not (= i (= (_ bv1 6) (ite Ve (_ bv0 6) (_ bv1 6))))) 
(and 
  x9 
  (or 
    (and x815 x8 x24 x814 x81 x7 x23 x82 x2 x238 x37 x3 (ite x9 false r) (= e (_ bv0 6))) 
    (and x9 (= e (ite x9 (_ bv1 6) er)) (= e (ite x815 (_ bv0 6) (ite x82 (_ bv0 6) (ite x815 (_ bv0 6) (ite x9 er (ite ri (_ bv0 6) (_ bv1 6)))))))))
)))))
(check-sat)
