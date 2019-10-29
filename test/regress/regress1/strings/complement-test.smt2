(set-logic SLIA)
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= x (str.++ "AB" y)))
(assert (or (= y "C") (= y (str.++ "D" z)) (= (str.len y) 10)))
(assert (str.in.re x 
            (re.inter 
              (re.complement (str.to.re "AB")) 
              (re.complement (re.++ (str.to.re "AB") (re.range "A" "E") (re.* re.allchar))))))
(check-sat)
