; EXPECT: sat
(set-logic ALL)
(declare-const x String)
(set-option :cbqi-eager-test false)
(set-option :cbqi-tconstraint true)
(check-sat-assuming ((= x (str.replace_re_all x (str.to_re x) x))))
