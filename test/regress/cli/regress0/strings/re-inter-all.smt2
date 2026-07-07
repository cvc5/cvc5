; EXPECT: unsat
(set-logic ALL)
(declare-const s String)
(declare-const r1 RegLan)
(declare-const r2 RegLan)
(assert (str.in_re s (re.* (re.inter (re.range "A" "Z") (re.range "B" "Z")))))
(assert (not (str.in_re s (re.* (re.inter (re.range "A" "Z") (re.* re.allchar) (re.range "B" "Z"))))))
(check-sat)
