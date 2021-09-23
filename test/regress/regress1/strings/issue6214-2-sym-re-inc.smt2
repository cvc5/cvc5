; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () String)
(declare-fun b () String)
(assert (str.in_re a (re.range "a" "c")))
(assert
 (str.in_re a
  (re.*
   (re.union
    (re.++ (re.union (str.to_re "a") (str.to_re "b")) (str.to_re "a"))
    (str.to_re (str.from_int (str.len b)))))))
(check-sat)
