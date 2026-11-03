; REQUIRES: unrestricted-mode
; COMMAND-LINE: --theoryof-mode=type --no-pp-ite-lift
; COMMAND-LINE: --theoryof-mode=term --no-pp-ite-lift
; SCRUBBER: grep -o "ITE branches of type RegLan are currently not supported"
; EXPECT: ITE branches of type RegLan are currently not supported
; EXIT: 1 
(set-logic QF_SLIA)
(declare-const b Bool)
(declare-const x String)
(assert (str.in_re x (ite b re.none re.allchar)))
(check-sat)
