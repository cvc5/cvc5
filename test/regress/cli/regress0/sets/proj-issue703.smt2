; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-option :debug-check-models true)
(declare-const x String)
(check-sat-assuming ((str.is_digit (set.choose (set.insert "" (set.singleton x))))))
