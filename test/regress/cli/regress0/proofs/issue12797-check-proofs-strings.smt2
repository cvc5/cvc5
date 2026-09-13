; COMMAND-LINE: --check-proofs
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () String)
(declare-fun b () String)
(assert
 (str.in_re
  (str.replace_re a
                  (str.to_re (str.replace_all "a" (str.++ a a) b))
                  (str.++ b a))
  (re.* (str.to_re "b"))))
(assert (str.in_re a (re.+ (re.range "a" "a"))))
(check-sat)
