; Regression for higher-order set.filter model construction/checking.
; The predicate (lambda (e) (r e c)) applies the relation r to the bound
; variable in a non-tail (non-curry-friendly) position. The model is sound;
; this used to trip --check-models because the function value was returned
; unevaluated inside the predicate lambda. See theory_model.cpp getModelValue.
(set-logic HO_ALL)
(set-option :produce-models true)
(set-info :status sat)
(declare-fun r (Int Int) Bool)
(declare-const A (Set Int))
(declare-const c Int)
(declare-const y Int)
(declare-const w Int)
(assert (set.member c A))
(assert (set.member y A))
(assert (set.member w A))
(assert (distinct c y w))
(assert (= A (set.filter (lambda ((e Int)) (r e c)) A)))
(check-sat)
