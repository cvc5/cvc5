; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(set-option :nl-ext-ent-conf true)
(declare-const x Int)
(assert (> (* x x) (+ x x)))
(assert (not (str.is_digit (str.from_code x))))
(check-sat)
