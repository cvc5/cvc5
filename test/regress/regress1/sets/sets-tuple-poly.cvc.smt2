; COMMAND-LINE:
; EXPECT: sat
(set-option :incremental false)
(set-option :sets-ext true)
(set-logic ALL)
(declare-fun a () (Set (Tuple Real Int)))
(declare-fun b () (Set (Tuple Int Real)))
(declare-fun x () (Tuple Real Real))
(assert (let ((_let_1 0.0)) (not (= x (mkTuple _let_1 _let_1)))))
(assert (member (mkTuple ((_ tupSel 0) x) (to_int ((_ tupSel 1) x))) a))
(assert (member (mkTuple (to_int ((_ tupSel 0) x)) ((_ tupSel 1) x)) b))
(assert (not (= ((_ tupSel 0) x) ((_ tupSel 1) x))))
(check-sat)
