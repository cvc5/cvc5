; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun s () String)

(assert (or
(= (str.++ s "A") "")
(= (str.++ s s) "A")
(not (str.contains s ""))
(str.contains "" (str.++ s "A"))
(not (= (str.replace "A" s "A") "A"))
(not (= (str.prefixof s "A") (str.suffixof s "A")))
(not (str.prefixof s s))
(not (str.prefixof "" s))
)
)
(check-sat)
