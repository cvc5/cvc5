; EXPECT: unsat
; Regression for CPC proof checking of re-union-inclusion where the included
; regular expression is a single non-string component (a range) and the
; including regular expression is a concatenation.
(set-logic QF_S)
(declare-const s String)
(assert (not (str.in_re s (re.union (re.++ (re.* re.allchar) (re.range "a" "c"))
                                    (re.comp (re.range "a" "c"))))))
(check-sat)
