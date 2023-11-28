; COMMAND-LINE: --no-strings-lazy-pp
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun a () String)
(declare-fun b () String)
(assert (str.in_re (str.++ b "z" a) (re.++ (re.* (re.++ (str.to_re "z") (re.* (str.to_re "b")))) (str.to_re "b"))))
(assert (not (str.in_re (str.++ b "a") (re.* (re.++ (re.* (str.to_re "b")) (re.diff (str.to_re (str.from_int (str.len b))) (str.to_re (str.replace a b ""))))))))
(check-sat)
