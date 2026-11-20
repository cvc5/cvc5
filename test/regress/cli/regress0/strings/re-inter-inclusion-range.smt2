; EXPECT: unsat
; Regression for CPC proof checking of the RE_ANDOR_INC_CONFLICT rewrite
; (rule re-inter-inclusion), where the included regular expression is a single
; non-string component (here a range).
(set-logic QF_S)
(declare-const s String)
(assert (str.in_re s (re.inter (re.range "a" "c")
                               (re.comp (re.++ (re.range "a" "c") (re.* re.allchar))))))
(check-sat)
