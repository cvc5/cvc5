; COMMAND-LINE: --fp-exp
; EXPECT: sat
(set-logic ALL)
(declare-const x Float128)
(declare-const _x String)
(declare-fun x5 (Bool Float128) Bool)
(check-sat-assuming ((x5 (exists ((x (Array String Bool))) (and (select x _x) (or (select x _x) (x5 (exists ((x Bool)) true) (_ -oo 15 113))))) x)))
