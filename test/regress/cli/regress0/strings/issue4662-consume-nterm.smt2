; COMMAND-LINE: 
; COMMAND-LINE: --strings-re-derive-conf
(set-logic QF_S)
(set-info :status unsat)
(declare-fun a () String)
(define-fun b () RegLan (str.to_re "A"))
(assert (str.in_re (str.++ "B" a) (re.+ (re.++ (re.opt b) (re.opt b)))))
(check-sat)
