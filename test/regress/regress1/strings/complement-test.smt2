(set-logic SLIA)
(set-option :strings-exp true)
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= x (str.++ "AB" y)))
(assert (or (= y "C") (= y (str.++ "D" z)) (= (str.len y) 10)))
(assert (str.in_re x 
            (re.inter 
              (re.comp (str.to_re "AB")) 
              (re.comp (re.++ (str.to_re "AB") (re.range "A" "E") (re.* re.allchar))))))
(check-sat)
