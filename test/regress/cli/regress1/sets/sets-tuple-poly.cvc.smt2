; COMMAND-LINE:
; EXPECT: sat
(set-option :incremental false)
(set-option :sets-ext true)
(set-logic ALL)
(declare-fun a () (Relation Real Int))
(declare-fun b () (Relation Int Real))
(declare-fun x () (Tuple Real Real))
(assert (let ((_let_1 0.0)) (not (= x (tuple _let_1 _let_1)))))
(assert (set.member (tuple ((_ tuple.select 0) x) (to_int ((_ tuple.select 1) x))) a))
(assert (set.member (tuple (to_int ((_ tuple.select 0) x)) ((_ tuple.select 1) x)) b))
(assert (not (= ((_ tuple.select 0) x) ((_ tuple.select 1) x))))
(check-sat)
