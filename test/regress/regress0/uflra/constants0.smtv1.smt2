; COMMAND-LINE: --no-check-proofs
(set-option :incremental false)
(set-info :status unsat)
(set-info :category "crafted")
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(check-sat-assuming ( (let ((_let_0 (f x))) (let ((_let_1 (f y))) (let ((_let_2 (f 3.0))) (let ((_let_3 (f 5.0))) (and (or (= x 3.0) (= x 5.0)) (or (= y 3.0) (= y 5.0)) (not (= _let_0 _let_1)) (=> (= _let_2 _let_0) (= _let_3 _let_0)) (=> (= _let_2 _let_1) (= _let_3 _let_1))))))) ))
