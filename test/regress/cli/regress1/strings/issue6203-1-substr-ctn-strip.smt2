; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)
(declare-fun e () String)
(assert (or (= (str.++ c (str.substr e (* (mod 0 0) (str.len b)) (str.len d))) "ab") (= (str.++ c (str.substr e (* (mod 0 0) (str.len b)) (str.len d))) "")))
(assert (= (str.len c) (+ (str.len e) (* (str.indexof a "a" 0) (str.len b))) 1 (str.len b)))
(check-sat)
