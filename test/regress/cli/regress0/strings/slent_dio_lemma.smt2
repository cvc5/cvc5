; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(assert (= 30 (+ (str.len x) (str.len (str.++ "\u{" (str.replace x ".g" ""))))))
(check-sat)
