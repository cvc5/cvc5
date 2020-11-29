; COMMAND-LINE: --fmf-bound
; EXPECT: unsat
(set-logic AUFNIA)
(declare-fun a () Int)
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun d () Int)
(assert
 (exists ((e Int))
 (and (<= e 0)
  (exists ((f Int))
  (and (<= 0 f e)
   (> (select (store b 0 (select c (div a d))) f)
   (select (store b 0 (select c (div a d))) e)))))))
(check-sat)
