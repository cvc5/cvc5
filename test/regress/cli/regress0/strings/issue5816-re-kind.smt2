; COMMAND-LINE: --no-strings-code-elim
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-const x String)
(declare-const x8 String)
(assert (str.in_re x8 (re.++ (str.to_re x) (re.range "a" "u"))))
(check-sat)
