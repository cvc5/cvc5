; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(define-fun x () (Tuple Real Int Real) (tuple (/ 4 5) 9 (/ 11 9)))
(define-fun first_elem () Real ((_ tuple.select 0) (tuple (/ 4 5) 9 (/ 11 9))))
(define-fun third_elem () Real ((_ tuple.select 2) (tuple (/ 4 5) 9 (/ 11 9))))

(define-fun y () (Tuple Real Int Real) (tuple (/ 4 5) 9 (/ 11 9)))
(define-fun y1 () (Tuple Real Int Real) ((_ tuple.update 1) (tuple (/ 4 5) 9 (/ 11 9)) 3))
(check-sat-assuming ( (not (let ((_let_1 (tuple (/ 4 5) 9 (/ 11 9)))) (let ((_let_2 ((_ tuple.update 1) _let_1 3))) (and (and (and (= _let_1 _let_1) (= ((_ tuple.select 0) _let_1) ((_ tuple.select 0) _let_2))) (= ((_ tuple.select 2) _let_1) ((_ tuple.select 2) _let_2))) (= ((_ tuple.select 1) _let_2) 3))))) ))
