; EXPECT: unsat
(set-logic ALL)
(declare-fun t () String)
(assert

(let ((_let_1 (str.substr t 0 (+ (- 1) (str.len (str.substr t 0 (+ (- 1) (str.len t)))))))) (let ((_let_2 (str.substr _let_1 0 (+ (- 1) (str.len (str.substr _let_1 0 (+ (- 1) (str.len _let_1)))))))) (let ((_let_3 (str.substr _let_2 0 (+ (- 1) (str.len (str.substr _let_2 0 (+ (- 1) (str.len _let_2)))))))) (let ((_let_4 (str.substr _let_3 0 (+ (- 1) (str.len (str.substr _let_3 0 (+ (- 1) (str.len _let_3)))))))) (let ((_let_5 (str.substr _let_4 0 (+ (- 1) (str.len (str.substr _let_4 0 (+ (- 1) (str.len _let_4)))))))) (let ((_let_6 (str.substr _let_5 0 (+ (- 1) (str.len (str.substr _let_5 0 (+ (- 1) (str.len _let_5)))))))) (let ((_let_7 (str.substr _let_6 0 (+ (- 1) (str.len (str.substr _let_6 0 (+ (- 1) (str.len _let_6)))))))) (let ((_let_8 (str.substr _let_7 0 (+ (- 1) (str.len (str.substr _let_7 0 (+ (- 1) (str.len _let_7)))))))) (let ((_let_9 (str.substr _let_8 0 (+ (- 1) (str.len (str.substr _let_8 0 (+ (- 1) (str.len _let_8)))))))) (let ((_let_10 (str.substr _let_9 0 (+ (- 1) (str.len (str.substr _let_9 0 (+ (- 1) (str.len _let_9)))))))) (let ((_let_11 (str.substr _let_10 0 (+ (- 1) (str.len (str.substr _let_10 0 (+ (- 1) (str.len _let_10)))))))) (let ((_let_12 (str.substr _let_11 0 (+ (- 1) (str.len (str.substr _let_11 0 (+ (- 1) (str.len _let_11)))))))) (let ((x (str.substr _let_12 0 (+ (- 1) (str.len (str.substr _let_12 0 (+ (- 1) (str.len _let_12))))))))


(not
(= (str.substr (str.substr x 0 (+ (- 1) (str.len x))) 0 (+ (- 1) (str.len (str.substr x 0 (+ (- 1) (str.len x)))))) 
(str.substr x (+ 0 0) (+ (- 1) (str.len (str.substr x 0 (+ (- 1) (str.len x)))))))
)

))))))))))))))
(check-sat)
