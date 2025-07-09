; COMMAND-LINE:
; COMMAND-LINE: --proof-cpc-str-in-re-nfa
(set-logic QF_SLIA)
(set-info :status unsat)
(assert (str.in_re "" (str.to_re "b")))
(check-sat)
