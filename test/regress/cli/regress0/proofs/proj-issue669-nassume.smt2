; EXPECT: sat
(set-logic ALL)
(set-option :incremental true)
(set-option :produce-unsat-cores true)
(set-option :proof-mode sat-proof)
(declare-const x String)
(assert (str.in_re (str.replace_re x re.none x) re.allchar))
(check-sat-assuming (true))
