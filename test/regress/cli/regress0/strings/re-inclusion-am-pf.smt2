; EXPECT: sat
(set-logic ALL)
(declare-fun x () String)

(assert (str.in_re x (re.++
                        (re.union (re.+ (str.to_re "A")) (re.inter (re.comp (re.++ re.allchar re.allchar (re.* re.allchar))) re.allchar))
                        (re.* re.allchar))))

(assert (str.in_re x (re.++ (str.to_re "B") (re.* re.allchar))))

(check-sat)
