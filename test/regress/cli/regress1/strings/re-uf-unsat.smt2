; COMMAND-LINE: --re-first-class
; EXPECT: unsat
(set-logic ALL)
(declare-fun f (RegLan) Int)
(declare-fun s () String)
(declare-fun x () Int)
(assert (< x (- 4)))
(assert (not (= (f (re.++ (str.to_re s) (re.* (str.to_re "A")))) (f (re.+ (str.to_re "A"))))))
(assert (or (> x 0) (= s "A")))
(check-sat)
