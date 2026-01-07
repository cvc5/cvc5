; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String) 
(declare-fun d () String)
(declare-fun f () String)
(declare-fun e () String)
(assert (and (not (str.contains f "E")) (not (str.contains f "D")) (not (str.contains f "C")))) 
(assert (and (not (<= 0 (+ (str.indexof (str.substr (str.substr b 0 (str.len d)) 0 (-
(str.indexof d "=" 0))) "N" 0) 1)))))
(assert (= (and (not (str.contains f "E")) (not (str.contains f "D")) (not (str.contains f "C")))
(= (str.replace (str.replace a c "") "" "") "")))
(assert (= a (str.++ (str.++ c "") e) b))
(check-sat)
