; COMMAND-LINE: --strings-exp --re-elim=agg
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () String)
(assert (str.in_re (str.replace_re a (re.++ (str.to_re "A") (re.union (str.to_re "") (str.to_re (str.from_code (str.len a))))) "AB") (re.+ (str.to_re "A"))))
(check-sat)
