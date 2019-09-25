(set-option :incremental false)
(set-info :source "We verify the correctness of an unsigned multiplication
overflow detection unit, which is described in
\"Combined Unsigned and Two's Complement Saturating Multipliers\"
by M. Schulte et al.

Bit-width: 4

Contributed by Robert Brummayer (robert.brummayer@gmail.com).")
(set-info :status unsat)
(set-info :category "industrial")
(set-info :difficulty "0")
(set-logic QF_BV)
(declare-fun v1 () (_ BitVec 4))
(declare-fun v2 () (_ BitVec 4))
(check-sat-assuming ( (let ((_let_0 (bvand (bvnot ((_ extract 3 3) v2)) (bvnot ((_ extract 2 2) v2))))) (not (= (bvnot (ite (= (bvnot (ite (= ((_ extract 7 4) (bvmul (concat (_ bv0 4) v1) (concat (_ bv0 4) v2))) (_ bv0 4)) (_ bv1 1) (_ bv0 1))) (bvnot (bvand (bvand (bvand (bvnot (bvand ((_ extract 1 1) v1) ((_ extract 3 3) v2))) (bvnot (bvand ((_ extract 2 2) v1) (bvnot _let_0)))) (bvnot (bvand ((_ extract 3 3) v1) (bvnot (bvand _let_0 (bvnot ((_ extract 1 1) v2))))))) (bvnot ((_ extract 4 4) (bvmul (concat (_ bv0 1) v1) (concat (_ bv0 1) v2))))))) (_ bv1 1) (_ bv0 1))) (_ bv0 1)))) ))
