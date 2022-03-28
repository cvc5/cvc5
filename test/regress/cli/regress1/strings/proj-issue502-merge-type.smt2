; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :strings-exp true)
(check-sat-assuming ((seq.nth (seq.unit (is_int (seq.nth (seq.unit real.pi) 1))) (to_int (seq.nth (seq.unit real.pi) 1)))))
