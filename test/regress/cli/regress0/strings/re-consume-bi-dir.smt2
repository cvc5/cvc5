
(declare-fun k () String)
(assert (not (str.in_re 
(str.++ "d.1.a" k "3") 
(re.++ (str.to_re "d.") (re.* (re.range "0" "9")) (str.to_re ".") (re.* re.allchar))
)))
(check-sat)

(exit)


(alf.requires 

((str.in_re ((str.++ "a") ((str.++ k) ((str.++ "3") "")))) (re.* re.allchar)) 
((str.in_re ((str.++ "a") ((str.++ k) ""))) (re.* re.allchar)) 

(Proof ((= ((str.in_re ((str.++ "d.1.a") ((str.++ k) ((str.++ "3") "")))) ((re.++ (str.to_re "d.")) ((re.++ (re.* ((re.range "0") "9"))) ((re.++ (str.to_re ".")) ((re.++ (re.* re.allchar)) (str.to_re ""))))))) ((str.in_re ((str.++ "a") ((str.++ k) ""))) (re.* re.allchar)))))
