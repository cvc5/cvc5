; EXPECT: unsat
(set-logic ALL)
(declare-fun purify_81 () String)
(declare-fun purify_82 () String)
(assert (not
(= (str.replace (str.++ purify_81 "A" purify_82) "A" "a") (str.++ (str.replace (str.++ purify_81 "A") "A" "a") purify_82))
))
(check-sat)
