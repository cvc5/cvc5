; EXPECT: true
(set-logic SLIA)
(get-qe (exists ((x String)) (not (= (str.in_re x (re.* (str.to_re "A"))) (str.in_re x (re.* (str.to_re "B")))))))
