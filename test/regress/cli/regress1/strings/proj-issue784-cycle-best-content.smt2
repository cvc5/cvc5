; EXPECT: unsat
(set-logic ALL)
(declare-fun a () String)
(assert (str.suffixof "B" (str.replace (str.++ (str.++ "B" a) "B")
(str.replace_all (str.++ (str.++ (str.replace_all "B"
(str.replace_all (str.++ a "") "" "") "B") a) "B") "" (str.++ (str.++
(str.replace_all "" (str.replace_all (str.++ a "") "" "") "") a) ""))
(str.++ "" ""))))
(check-sat)
