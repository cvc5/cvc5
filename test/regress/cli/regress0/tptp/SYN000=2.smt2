;; Input has to_int applied to an integer
; DISABLE-TESTER: alethe
(set-logic ALL)
(set-info :status unsat)
(declare-sort $$unsorted 0)
(declare-fun tptp.p_int (Int) Bool)
(declare-fun tptp.p_rat (Real) Bool)
(declare-fun tptp.p_real (Real) Bool)
(declare-fun tptp.a_int () Int)
(declare-fun tptp.a_rat () Real)
(declare-fun tptp.a_real () Real)
(assert (or (tptp.p_int 123) (tptp.p_int (- 123))))
(assert (let ((_let_1 (tptp.p_rat (/ 41 152)))) (or _let_1 (tptp.p_rat (/ (- 41) 152)) _let_1)))
(assert (let ((_let_1 (tptp.p_real 123456000000000000000000000000000000000000000000000000000000000000000000000000000.0))) (or (tptp.p_real (/ 15432 125)) (tptp.p_real (/ (- 15432) 125)) _let_1 _let_1 (tptp.p_real (- 123456000000000000000000000000000000000000000000000000000000000000000000000000000.0)) (tptp.p_real (/ 1929 15625000000000000000000000000000000000000000000000000000000000000000000000000000)) (tptp.p_real (/ (- 1929) 15625000000000000000000000000000000000000000000000000000000000000000000000000000)))))
(assert (forall ((X Int)) (exists ((Y Int)) (=> (tptp.p_int X) (tptp.p_int Y)))))
(assert (forall ((X Real)) (exists ((Y Real)) (=> (tptp.p_rat X) (tptp.p_rat Y)))))
(assert (forall ((X Real)) (exists ((Y Real)) (=> (tptp.p_real X) (tptp.p_real Y)))))
(assert (< tptp.a_int 3))
(assert (< tptp.a_rat (/ 1 3)))
(assert (< tptp.a_real (/ 33 10)))
(assert (<= tptp.a_int 3))
(assert (<= tptp.a_rat (/ 1 3)))
(assert (<= tptp.a_real (/ 33 10)))
(assert (> tptp.a_int (- 3)))
(assert (> tptp.a_rat (/ (- 1) 3)))
(assert (> tptp.a_real (/ (- 33) 10)))
(assert (>= tptp.a_int (- 3)))
(assert (>= tptp.a_rat (/ (- 1) 3)))
(assert (>= tptp.a_real (/ (- 33) 10)))
(assert (= tptp.a_int 0))
(assert (= tptp.a_rat 0.0))
(assert (= tptp.a_real 0.0))
(assert (tptp.p_int (- 3)))
(assert (tptp.p_rat (- (/ 1 3))))
(assert (tptp.p_real (- (/ 33 10))))
(assert (tptp.p_int (+ 3 3)))
(assert (tptp.p_rat (+ (/ 1 3) (/ 1 3))))
(assert (tptp.p_real (+ (/ 33 10) (/ 33 10))))
(assert (tptp.p_int (- 3 3)))
(assert (tptp.p_rat (- (/ 1 3) (/ 1 3))))
(assert (tptp.p_real (- (/ 33 10) (/ 33 10))))
(assert (tptp.p_int (* 3 3)))
(assert (tptp.p_rat (* (/ 1 3) (/ 1 3))))
(assert (tptp.p_real (* (/ 33 10) (/ 33 10))))
(assert (tptp.p_rat (/ (/ 1 3) (/ 1 3))))
(assert (tptp.p_real (/ (/ 33 10) (/ 33 10))))
(assert (let ((_let_1 (to_real 3))) (let ((_let_2 (/ _let_1 _let_1))) (tptp.p_int (ite (>= _let_1 0.0) (to_int _let_2) (- (to_int (- _let_2))))))))
(assert (let ((_let_1 (/ (/ 1 3) (/ 1 3)))) (tptp.p_rat (to_real (ite (>= (/ 1 3) 0.0) (to_int _let_1) (- (to_int (- _let_1))))))))
(assert (let ((_let_1 (/ (/ 33 10) (/ 33 10)))) (tptp.p_real (to_real (ite (>= (/ 33 10) 0.0) (to_int _let_1) (- (to_int (- _let_1))))))))
(assert (let ((_let_1 (to_real 3))) (let ((_let_2 (/ _let_1 _let_1))) (tptp.p_int (ite (>= _let_2 0.0) (to_int _let_2) (- (to_int (- _let_2))))))))
(assert (let ((_let_1 (/ (/ 1 3) (/ 1 3)))) (tptp.p_rat (to_real (ite (>= _let_1 0.0) (to_int _let_1) (- (to_int (- _let_1))))))))
(assert (let ((_let_1 (/ (/ 33 10) (/ 33 10)))) (tptp.p_real (to_real (ite (>= _let_1 0.0) (to_int _let_1) (- (to_int (- _let_1))))))))
(assert (let ((_let_1 (to_real 3))) (tptp.p_int (to_int (/ _let_1 _let_1)))))
(assert (tptp.p_rat (to_real (to_int (/ (/ 1 3) (/ 1 3))))))
(assert (tptp.p_real (to_real (to_int (/ (/ 33 10) (/ 33 10))))))
(assert (let ((_let_1 (to_real 3))) (let ((_let_2 (/ _let_1 _let_1))) (tptp.p_int (to_int (- _let_1 (* (ite (>= _let_1 0.0) (to_int _let_2) (- (to_int (- _let_2)))) _let_1)))))))
(assert (let ((_let_1 (/ (/ 1 3) (/ 1 3)))) (tptp.p_rat (to_real (to_int (- (/ 1 3) (* (ite (>= (/ 1 3) 0.0) (to_int _let_1) (- (to_int (- _let_1)))) (/ 1 3))))))))
(assert (let ((_let_1 (/ (/ 33 10) (/ 33 10)))) (tptp.p_real (to_real (to_int (- (/ 33 10) (* (ite (>= (/ 33 10) 0.0) (to_int _let_1) (- (to_int (- _let_1)))) (/ 33 10))))))))
(assert (let ((_let_1 (to_real 3))) (let ((_let_2 (/ _let_1 _let_1))) (tptp.p_int (to_int (- _let_1 (* (ite (>= _let_2 0.0) (to_int _let_2) (- (to_int (- _let_2)))) _let_1)))))))
(assert (let ((_let_1 (/ (/ 1 3) (/ 1 3)))) (tptp.p_rat (to_real (to_int (- (/ 1 3) (* (ite (>= _let_1 0.0) (to_int _let_1) (- (to_int (- _let_1)))) (/ 1 3))))))))
(assert (let ((_let_1 (/ (/ 33 10) (/ 33 10)))) (tptp.p_real (to_real (to_int (- (/ 33 10) (* (ite (>= _let_1 0.0) (to_int _let_1) (- (to_int (- _let_1)))) (/ 33 10))))))))
(assert (let ((_let_1 (to_real 3))) (tptp.p_int (to_int (- _let_1 (* (to_int (/ _let_1 _let_1)) _let_1))))))
(assert (tptp.p_rat (to_real (to_int (- (/ 1 3) (* (to_int (/ (/ 1 3) (/ 1 3))) (/ 1 3)))))))
(assert (tptp.p_real (to_real (to_int (- (/ 33 10) (* (to_int (/ (/ 33 10) (/ 33 10))) (/ 33 10)))))))
(assert (tptp.p_int (to_int 3)))
(assert (tptp.p_rat (to_real (to_int (/ 1 3)))))
(assert (tptp.p_real (to_real (to_int (/ 33 10)))))
(assert (tptp.p_int (- (to_int (- (to_real 3))))))
(assert (tptp.p_rat (to_real (- (to_int (- (/ 1 3)))))))
(assert (tptp.p_real (to_real (- (to_int (- (/ 33 10)))))))
(assert (let ((_let_1 (to_real 3))) (tptp.p_int (ite (>= _let_1 0.0) (to_int _let_1) (- (to_int (- _let_1)))))))
(assert (tptp.p_rat (to_real (ite (>= (/ 1 3) 0.0) (to_int (/ 1 3)) (- (to_int (- (/ 1 3))))))))
(assert (tptp.p_real (to_real (ite (>= (/ 33 10) 0.0) (to_int (/ 33 10)) (- (to_int (- (/ 33 10))))))))
(assert (exists ((X Int)) (is_int X)))
(assert (exists ((X Real)) (is_int X)))
(assert (exists ((X Real)) (is_int X)))
(assert (exists ((X Real)) (exists ((Q Int) (R Int)) (and (not (= R 0)) (= (to_real Q) (* X (to_real R)))))))
(assert (exists ((X Real)) (exists ((Q Int) (R Int)) (and (not (= R 0)) (= (to_real Q) (* X (to_real R)))))))
(assert (tptp.p_int (to_int 3)))
(assert (tptp.p_int (to_int (/ 1 3))))
(assert (tptp.p_int (to_int (/ 33 10))))
(assert (tptp.p_rat (to_real 3)))
(assert (tptp.p_rat (/ 1 3)))
(assert (tptp.p_rat (/ 33 10)))
(assert (tptp.p_real (to_real 3)))
(assert (tptp.p_real (/ 1 3)))
(assert (tptp.p_real (/ 33 10)))
(assert (not (exists ((X Int) (Y Real) (Z Real)) (and (= Y (to_real (+ X 2))) (or (< (to_int Y) 3) (> Y (/ 33 10)))))))
(set-info :filename SYN000=2)
(check-sat-assuming ( true ))
