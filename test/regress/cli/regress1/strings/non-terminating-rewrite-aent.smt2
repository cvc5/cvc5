; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(assert 
(let ((_let_1 (str.len a))) (let ((_let_2 (str.len b))) (let ((_let_3 (+ _let_1 (* (- 1) _let_2)))) (let ((_let_4 (ite (>= _let_3 1) (str.substr a 0 _let_3) (str.substr b 0 (+ (* (- 1) _let_1) _let_2))))) (let ((_let_5 (str.len _let_4))) (let ((_let_6 (str.len c))) (let ((_let_7 (+ _let_6 (* (- 1) _let_5)))) (let ((_let_8 (ite (>= _let_7 0) (str.substr c _let_5 _let_7) (str.substr _let_4 _let_6 (+ (* (- 1) _let_6) _let_5))))) (let ((_let_9 (str.len _let_8))) (let ((_let_10 (ite (>= _let_1 _let_9) (str.substr a _let_9 (- _let_1 _let_9)) (str.substr _let_8 _let_1 (- _let_9 _let_1))))) (and (= _let_8 (str.++ a _let_10)) (not (= "" _let_10)) (>= (str.len _let_10) 1))))))))))))
)
(check-sat)
