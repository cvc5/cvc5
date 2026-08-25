; EXPECT: unsat
; Regression for CPC proof checking of the RE_INTER_INCLUSION rewrite when the
; two regular expressions share a compound re.inter component. The flat-form
; inclusion check ($str_re_includes_rec) must short-circuit on equal leading
; components; otherwise it fails to prove R1 is a subset of R2 here.
(set-logic QF_S)
(declare-const x String)
(define-fun INTER () RegLan
  (re.inter (re.union (str.to_re "zn-alfa-1") (str.to_re "zn-brav-2"))
            (re.++ (str.to_re "zn-") (re.* re.allchar))))
(define-fun R1 () RegLan (re.++ (str.to_re "tag:svc:module:") INTER (str.to_re ":operator")))
(define-fun R2 () RegLan (re.++ (str.to_re "tag:svc:module:") INTER (str.to_re ":operator") (re.* re.allchar)))
(assert (str.in_re x R1))
(assert (not (str.in_re x R2)))
(check-sat)
