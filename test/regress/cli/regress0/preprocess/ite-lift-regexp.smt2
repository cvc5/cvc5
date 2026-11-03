; COMMAND-LINE: --theoryof-mode=type
; COMMAND-LINE: --theoryof-mode=term
; EXPECT: unsat
; Lifting the if-then-else term out of the regular expression membership avoids
; if-then-else terms of type RegLan, which are not supported (see
; regress0/strings/proj-issue316-regexp-ite.smt2).
(set-logic QF_SLIA)
(declare-const b Bool)
(declare-const x String)
(assert (str.in_re x (ite b re.none re.allchar)))
(assert (= (str.len x) 2))
(check-sat)
