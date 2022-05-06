; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic SLIA)
(set-info :status unsat)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)

; these should all rewrite to false
(assert (or 

(not (= (str.substr (str.++ x "abc" y) 0 (+ (str.len x) 1)) (str.++ x "a")))
(not (= (str.substr (str.++ x "abc" y) (+ (str.len x) 1) (+ (* 2 (str.len y)) 7)) (str.++ "bc" y)))
(not (= (str.substr (str.++ x y) 0 (+ (str.len z) (* 2 (str.len x)) (* 2 (str.len y)))) (str.substr (str.++ x y) 0 (+ (str.len x) (str.len y)))))
(not (= (str.substr x (+ (str.len x) 1) 5) (str.substr y (- (- 1) (str.len z)) 5)))
(not (= (str.substr "abc" 100000000000000000000000000000000000000000000000000000000000000000000000000 5) ""))

))

(check-sat)
