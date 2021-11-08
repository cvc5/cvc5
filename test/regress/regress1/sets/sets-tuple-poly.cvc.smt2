; COMMAND-LINE:
; EXPECT: sat
(set-option :incremental false)
(set-option :sets-ext true)
(set-logic ALL)
(declare-fun a () (Set (Tuple Real Int)))
(declare-fun b () (Set (Tuple Int Real)))
(declare-fun x () (Tuple Real Real))
(assert (let ((_let_1 0.0)) (not (= x (tuple _let_1 _let_1)))))
(assert (set.member (tuple ((_ tuple_select 0) x) (to_int ((_ tuple_select 1) x))) a))
(assert (set.member (tuple (to_int ((_ tuple_select 0) x)) ((_ tuple_select 1) x)) b))
(assert (not (= ((_ tuple_select 0) x) ((_ tuple_select 1) x))))
(check-sat)
