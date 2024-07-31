; EXPECT: unsat
(set-logic QF_SLIA)
(declare-const X String)
(assert (str.in_re X (re.++ ((_ re.loop 1 1) (re.union (re.range "a" "z") (re.range "A" "Z"))) (re.++ (str.to_re "-") (re.++ (str.to_re ">") (re.++ (re.+ (re.union (re.range "a" "z") (re.range "A" "Z"))) (re.* (re.++ (str.to_re "|") (re.+ (re.union (re.range "a" "z") (re.range "A" "Z")))))))))))
; sanitize danger characters:  < > ' " &
(assert (not (str.in_re X (re.++ re.all (re.union (str.to_re "\u{3c}") (str.to_re "\u{3e}") (str.to_re "\u{27}") (str.to_re "\u{22}") (str.to_re "\u{26}")) re.all))))
(assert (< 20 (str.len X)))
(check-sat)
(exit)
