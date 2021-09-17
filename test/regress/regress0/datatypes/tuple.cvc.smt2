; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(define-fun x () (Tuple Real Int Real) (mkTuple (/ 4 5) 9 (/ 11 9)))
(define-fun first_elem () Real ((_ tupSel 0) (mkTuple (/ 4 5) 9 (/ 11 9))))
(define-fun third_elem () Real ((_ tupSel 2) (mkTuple (/ 4 5) 9 (/ 11 9))))

(define-fun y () (Tuple Real Int Real) (mkTuple (/ 4 5) 9 (/ 11 9)))
(define-fun y1 () (Tuple Real Int Real) ((_ update __cvc5_tuple_Real_Int_Real_stor_1) update___cvc5_tuple_Real_Int_Real_stor_1 (mkTuple (/ 4 5) 9 (/ 11 9)) 3))
(check-sat-assuming ( (not (let ((_let_1 (mkTuple (/ 4 5) 9 (/ 11 9)))) (let ((_let_2 ((_ update __cvc5_tuple_Real_Int_Real_stor_1) update___cvc5_tuple_Real_Int_Real_stor_1 _let_1 3))) (and (and (and (= _let_1 _let_1) (= ((_ tupSel 0) _let_1) ((_ tupSel 0) _let_2))) (= ((_ tupSel 2) _let_1) ((_ tupSel 2) _let_2))) (= ((_ tupSel 1) _let_2) 3))))) ))
