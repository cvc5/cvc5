; EXPECT: (error "expecting a constant string term in regexp range")
; EXIT: 1
(set-logic ALL)
(declare-const a String)
(declare-const b String)
(assert (not (str.in_re "a" (re.+ (re.range a b))))) 
(check-sat)
