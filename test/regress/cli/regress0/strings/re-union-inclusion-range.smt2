; EXPECT: unsat
; Regression for CPC proof checking of the RE_ANDOR_INC_CONFLICT rewrite
; (rule re-union-inclusion), where the included regular expression is a single
; non-string component (here a range). The proof checker must fall back to
; component-wise reasoning when the left-hand side is a concatenation.
(set-logic QF_S)
(declare-const s String)
(assert (not (str.in_re s (re.union (re.++ (re.range "a" "c") (re.* re.allchar))
                                    (re.comp (re.range "a" "c"))))))
(check-sat)
