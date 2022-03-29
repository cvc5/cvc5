; COMMAND-LINE: --lang=smt2.6
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () String)

(assert (or (str.in_re x re.none) (not (str.in_re x re.all))))

(check-sat)
