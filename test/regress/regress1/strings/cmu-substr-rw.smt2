(set-logic ALL)
(set-info :status sat)
(set-option :strings-exp true)

(declare-fun uri () String)

(assert (and (and (and (and (and (and (and (and (and (and (and (and (not (not (= (ite (= (str.len (str.substr (str.substr uri (+ (str.indexof uri "%" 0) 1) (- (str.len uri) (+ (str.indexof uri "%" 0) 1))) 0 (- 2 0))) 2) 1 0) 0))) (not (not (= (ite (str.contains (str.substr uri (+ (str.indexof uri "%" 0) 1) (- (str.len uri) (+ (str.indexof uri "%" 0) 1))) "%") 1 0) 0)))) (not (not (= (ite (= (str.len (str.substr uri (+ (str.indexof uri "%" 0) 1) (- (str.len uri) (+ (str.indexof uri "%" 0) 1)))) 0) 1 0) 0)))) (not (= (ite (str.contains uri "%") 1 0) 0))) (not (not (= (ite (= (str.len uri) 0) 1 0) 0)))) (>= (+ (str.indexof uri "%" 0) 1) 0)) (>= (- (str.len uri) (+ (str.indexof uri "%" 0) 1)) 0)) (>= 0 0)) (>= (- 2 0) 0)) (>= (+ (str.indexof uri "%" 0) 1) 0)) (>= (- (str.len uri) (+ (str.indexof uri "%" 0) 1)) 0)) (>= (+ (str.indexof uri "%" 0) 1) 0)) (>= (- (str.len uri) (+ (str.indexof uri "%" 0) 1)) 0)))

(check-sat)

