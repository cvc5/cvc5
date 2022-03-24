(set-logic QF_ABV)
(set-info :status unsat)
(declare-fun x2 () (_ BitVec 32))
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun x3 () (_ BitVec 32))

(assert (not (=
(store (store (store a x2 (select a (bvadd x2 (_ bv1 32))))
	      (bvadd x2 (_ bv1 32)) (select a (bvadd x2 (_ bv1 32))))
       x2 (select a x2))

       a)))
(check-sat)
(exit)
