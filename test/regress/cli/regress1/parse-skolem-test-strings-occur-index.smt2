; COMMAND-LINE: --parse-skolem-definitions --print-skolem-definitions
; EXPECT: sat
(set-option :parse-skolem-definitions true)
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun x () String)
(assert (not (>= (+ (str.indexof x "\u{0}" (@strings_occur_index x "\u{0}" (@strings_num_occur x "\u{0}"))) (* (- 1) (str.len x))) 1)))
(check-sat)
