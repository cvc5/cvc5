; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic SLIA)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)

; these should all rewrite to false
(assert (or
(str.contains "abcdef0ghij1abced" (str.++ "g" (str.from_int (str.len z)) x "a" y (str.from_int (+ (str.len z) 1))))
(str.contains "abc23cd" (str.++ (str.from_int (str.len z)) (str.from_int (str.len z)) (str.from_int (str.len z))))
(not (str.contains (str.++ x "ab" y) (str.++ "b" (str.substr y 0 4))))
(not (str.contains (str.++ x "ab" y) (str.++ (str.substr x 5 (str.len x)) "a")))
(str.contains (str.++ x y) (str.++ x "a" y))
(str.contains (str.++ x y) (str.++ y x x y "a"))
)
) 

(check-sat)
