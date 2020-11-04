(set-logic QF_SLIA)
(declare-fun a () String)
(assert (not (= (ite (str.contains (str.++ (str.replace (str.substr
 (str.substr (str.substr a 1 (- (str.len a) 1)) 0 (- (str.len
 (str.substr a 1 (- (str.len a) 1))) 0)) 0 (- (+ (str.indexof (str.++
 (str.replace (str.substr (str.substr a 1 (- (str.len a) 1)) 0 1) "A"
 "") "") "D" 0) 1) 0)) "" "") (str.substr (str.substr (str.substr a 1
 (- (str.len a) 1)) 1 (str.len (str.substr a 1 (- (str.len a) 1)))) 0
 (str.len (str.substr (str.substr a 1 (- (str.len a) 1)) 0 (str.len
 (str.substr a 1 (- (str.len a) 1))))))) "F") 1 0) 0)))
(assert (= (ite (str.contains (str.substr (str.substr (str.substr a 1
 (- (str.len a) 1)) (+ (str.indexof (str.substr a 1 (- (str.len a)
 1)) "A" 0) 1) (str.len (str.substr a 1 (- (str.len a) 1)))) 0 (-
 (str.len (str.substr (str.substr a 1 (- (str.len a) 1)) 0 (str.len
 (str.substr a 1 (- (str.len a) 1))))) (+ (str.indexof (str.substr
 (str.substr a 1 (- (str.len a) 1)) 1 (str.len (str.substr a 1 (-
 (str.len a) 1)))) "D" 0) 1))) "D") 1 0) 0))
(assert (not (= (ite (str.contains (str.substr (str.substr a 1 (-
 (str.len a) 1)) 0 (str.len (str.substr a 1 (- (str.len a) 1)))) "D")
 1 0) 0)))
(assert (<= (+ (str.indexof (str.substr (str.substr a 1 (- (str.len a)
 1)) (+ (str.indexof (str.substr a 1 (- (str.len a) 1)) "A" 0) 1) (-
 (str.len (str.substr a 1 (- (str.len a) 1))) 0)) "D" 0) 1) 0))
(check-sat)
(exit)
(reset)
(set-logic QF_SLIA)
(define-fun a () String "IAFHD")
(assert (not (= (ite (str.contains (str.++ (str.replace (str.substr
 (str.substr (str.substr a 1 (- (str.len a) 1)) 0 (- (str.len
 (str.substr a 1 (- (str.len a) 1))) 0)) 0 (- (+ (str.indexof (str.++
 (str.replace (str.substr (str.substr a 1 (- (str.len a) 1)) 0 1) "A"
 "") "") "D" 0) 1) 0)) "" "") (str.substr (str.substr (str.substr a 1
 (- (str.len a) 1)) 1 (str.len (str.substr a 1 (- (str.len a) 1)))) 0
 (str.len (str.substr (str.substr a 1 (- (str.len a) 1)) 0 (str.len
 (str.substr a 1 (- (str.len a) 1))))))) "F") 1 0) 0)))
(assert (= (ite (str.contains (str.substr (str.substr (str.substr a 1
 (- (str.len a) 1)) (+ (str.indexof (str.substr a 1 (- (str.len a)
 1)) "A" 0) 1) (str.len (str.substr a 1 (- (str.len a) 1)))) 0 (-
 (str.len (str.substr (str.substr a 1 (- (str.len a) 1)) 0 (str.len
 (str.substr a 1 (- (str.len a) 1))))) (+ (str.indexof (str.substr
 (str.substr a 1 (- (str.len a) 1)) 1 (str.len (str.substr a 1 (-
 (str.len a) 1)))) "D" 0) 1))) "D") 1 0) 0))
(assert (not (= (ite (str.contains (str.substr (str.substr a 1 (-
 (str.len a) 1)) 0 (str.len (str.substr a 1 (- (str.len a) 1)))) "D")
 1 0) 0)))
(assert (<= (+ (str.indexof (str.substr (str.substr a 1 (- (str.len a)
 1)) (+ (str.indexof (str.substr a 1 (- (str.len a) 1)) "A" 0) 1) (-
 (str.len (str.substr a 1 (- (str.len a) 1))) 0)) "D" 0) 1) 0))
(check-sat)
