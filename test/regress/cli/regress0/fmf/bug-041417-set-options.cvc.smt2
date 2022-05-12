; EXPECT: sat
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :incremental false)
(set-option :finite-model-find true)
(set-option :fmf-fun true)
(declare-datatypes ((Node 0)) (((A) (B))))
(declare-fun link (Node Node Int) Bool)
(declare-fun reach (Node Node Int) Bool)
(assert (forall ((x Node) (y Node) (c Int)) (=> (link x y c) (reach x y c))))
(assert (link A B 1))
(check-sat-assuming ( (reach A B 5) ))
