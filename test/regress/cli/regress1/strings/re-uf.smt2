
(set-logic ALL)
(declare-fun f (RegLan) Int)
(declare-fun s () String)
(assert (not (= (f (re.++ (re.* (str.to_re "A")) (str.to_re s))) (f (re.+ (str.to_re "A"))))))
(assert (or (= s "A") (= s "AAA")))
(check-sat)
