; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((enum 0)) (((enum1) (enum2) (enum3) (enum4) (enum5) (enum6) (enum7) (enum8) (enum9) (enum10) (enum11) (enum12) (enum13) (enum14) (enum15) (enum16) (enum17) (enum18) (enum19) (enum20) (enum21) (enum22) (enum23) (enum24) (enum25) (enum26) (enum27) (enum28) (enum29) (enum30) (enum31) (enum32) (enum33))))
(declare-fun x () enum)
(declare-fun y () enum)
(assert (= x enum1))
(assert (= y enum33))
(check-sat-assuming ( (not (not (= x y))) ))
