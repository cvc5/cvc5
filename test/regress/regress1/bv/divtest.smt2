(set-logic QF_BV)
(set-info :status unsat)
(declare-fun x1 () (_ BitVec 12))
(declare-fun x2 () (_ BitVec 12))
(declare-fun x3 () (_ BitVec 12))

(declare-fun y1 () (_ BitVec 12))
(declare-fun y2 () (_ BitVec 12))
(declare-fun y3 () (_ BitVec 12))

(declare-fun z1 () (_ BitVec 12))
(declare-fun z2 () (_ BitVec 12))
(declare-fun z3 () (_ BitVec 12))

(declare-fun a () (_ BitVec 12))

(declare-fun x01 () (_ BitVec 10))
(declare-fun x02 () (_ BitVec 10))
(declare-fun x03 () (_ BitVec 10))

(declare-fun y01 () (_ BitVec 10))
(declare-fun y02 () (_ BitVec 10))
(declare-fun y03 () (_ BitVec 10))

(declare-fun z01 () (_ BitVec 10))
(declare-fun z02 () (_ BitVec 10))
(declare-fun z03 () (_ BitVec 10))

(declare-fun a0 () (_ BitVec 10))

(assert
(or 
(and 
	(= a (_ bv0 12))
	(or (not (= (bvudiv x1 a) (bvudiv x2 a)))
	    (not (= (bvudiv x1 a) (bvudiv x3 a)))
	    (not (= (bvudiv x2 a) (bvudiv x3 a))))
	(or (and (= x1 y1) (= y1 x2))
	    (and (= x1 z1) (= z1 x2)))
	(or (and (= x2 y2) (= y2 x3))
	    (and (= x2 z2) (= z2 x3))))

(and 
	(= a0 (_ bv0 10))
	(or (not (= (bvurem x01 a0) (bvurem x02 a0)))
	    (not (= (bvurem x01 a0) (bvurem x03 a0)))
	    (not (= (bvurem x02 a0) (bvurem x03 a0))))
	(or (and (= x01 y01) (= y01 x02))
	    (and (= x01 z01) (= z01 x02)))
	(or (and (= x02 y02) (= y02 x03))
	    (and (= x02 z02) (= z02 x03))))))
	    
(check-sat)
