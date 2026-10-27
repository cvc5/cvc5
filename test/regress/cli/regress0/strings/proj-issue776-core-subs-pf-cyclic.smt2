; EXPECT: unsat
(set-logic ALL)
(declare-fun a () String) (assert (distinct (str.contains (str.++ a "") (str.replace_all 
(str.replace_all (str.replace "" (str.++ a "") (str.++ (str.replace a "" a) "")) "" 
(str.replace "" (str.++ a "") (str.++ (str.replace a "" a) ""))) (str.++ "" "") 
(str.replace_all (str.replace "B" (str.++ a "") (str.++ (str.replace a "" a) "")) "" 
(str.replace "B" (str.++ a "B") (str.++ (str.replace a "B" a) "B"))))) (not (str.is_digit "")))) 
(check-sat)
