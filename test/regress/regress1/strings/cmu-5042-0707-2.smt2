(set-logic ALL_SUPPORTED)
(set-info :status sat)
(set-option :strings-exp true)

(declare-fun key2 () String)
(declare-fun key1 () String)

(assert 
(and 
(not 
(str.contains (str.++ (str.replace (str.substr key2 0 (- (+ (str.indexof key2 "X" 0) 1) 0)) "X" "x") (str.++ (str.replace (str.substr (str.substr key2 (+ (str.indexof key2 "X" 0) 1) (- (str.len key2) (+ (str.indexof key2 "X" 0) 1))) 0 (- (+ (str.indexof (str.substr key2 (+ (str.indexof key2 "X" 0) 1) (- (str.len key2) (+ (str.indexof key2 "X" 0) 1))) "X" 0) 1) 0)) "X" "x") (str.substr (str.substr key2 (+ (str.indexof key2 "X" 0) 1) (- (str.len key2) (+ (str.indexof key2 "X" 0) 1))) (+ (str.indexof (str.substr key2 (+ (str.indexof key2 "X" 0) 1) (- (str.len key2) (+ (str.indexof key2 "X" 0) 1))) "X" 0) 1) (- (str.len (str.substr key2 (+ (str.indexof key2 "X" 0) 1) (- (str.len key2) (+ (str.indexof key2 "X" 0) 1)))) (+ (str.indexof (str.substr key2 (+ (str.indexof key2 "X" 0) 1) (- (str.len key2) (+ (str.indexof key2 "X" 0) 1))) "X" 0) 1))))) "Z"))
(str.contains (str.substr key2 (+ (str.indexof key2 "X" 0) 1) (- (str.len key2) (+ (str.indexof key2 "X" 0) 1))) "X"))) 

(check-sat)

