; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(declare-const x3 Bool)
(declare-const x Int)
(declare-const w String)
(declare-const a String)
(assert (str.contains (str.substr (str.++ a ":" a w) 0 x) "-p"))
(assert (not (str.prefixof "abcdefghijklmnop" (str.++ "" a))))
(assert (or x3 (str.prefixof "ABCDEFGHIJKLMNO" (str.++ a ""))))
(assert (str.in_re a (re.* (re.range "a" "z"))))
(check-sat)
