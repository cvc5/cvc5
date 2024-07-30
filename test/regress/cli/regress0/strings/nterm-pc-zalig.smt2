; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(assert (not (= x "")))
(assert (str.in_re x (re.* (re.inter (re.++ (str.to_re "/filename=") (re.* (re.comp (str.to_re "\u{a}"))) (str.to_re ".plp/i\u{a}")) (re.comp (re.++ (re.* re.allchar) (re.union (re.range "a" "z") (re.range "A" "Z")) (str.to_re "\u{a}")))))))
(check-sat)
