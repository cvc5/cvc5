; EXPECT: unsat
(set-logic ALL)
(declare-fun s () String)
(assert (str.in_re s (re.++ (re.* (re.range "C" "E")) (re.range "B" "Y"))))
(assert (not (str.in_re s (re.++ (re.* re.allchar) (re.range "A" "Z")))))
(check-sat)
