; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-const x Int)
(check-sat-assuming ((str.< (str.++ (str.from_int x) (str.replace_re (str.from_int x) re.none (str.from_int 0)) (str.replace_re (str.from_int x) re.none (str.from_int 0))) (str.from_int x))))
