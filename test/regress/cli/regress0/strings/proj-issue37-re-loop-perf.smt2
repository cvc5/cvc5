; EXPECT: sat
(set-option :produce-models true)
(set-logic ALL)
(declare-fun v0 () String)
; at least 200 iterations of the regular expression r
(assert (str.in_re v0 (let ((r (re.++ (re.range "\u{d5}" "\u{e0}") (re.range "@" "^")))) (re.++ ((_ re.^ 200) r) (re.* r)))))
(check-sat)
