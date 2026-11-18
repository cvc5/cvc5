; EXPECT: ""
; EXPECT: ""
(set-logic ALL)
(declare-fun s () String)
(simplify (str.replace "" (str.++ s "A") s))
(simplify (str.replace_all "" (str.++ s "A") s))
