; EXPECT: true
; EXPECT: false
(set-logic SLIA)
(get-qe (exists ((x String)) (not (= (str.in_re x (re.* (str.to_re "A"))) 
                                     (str.in_re x (re.* (str.to_re "B")))))))
(get-qe (exists ((x String)) (not (= (str.in_re x (re.++ (str.to_re "A") (re.* (str.to_re "A")))) 
                                     (str.in_re x (re.++ (re.* (str.to_re "A")) (str.to_re "A")))))))
