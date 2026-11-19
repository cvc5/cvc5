; EXPECT: unsat
; Regression for CPC proof checking of re-union-inclusion where the included
; regular expression is a single non-string component (re.allchar) and the
; including regular expression is a concatenation.
(set-logic QF_S)
(declare-const s String)
(assert (not (str.in_re s (re.union (re.++ re.allchar (re.* re.allchar))
                                    (re.comp re.allchar)))))
(check-sat)
