; COMMAND-LINE: -i
; EXPECT: sat
(set-logic ALL)
(set-option :strings-lazy-pp false)
(set-info :status sat)
(declare-fun s () String)
(declare-fun t () String)
(declare-fun r () String)
(declare-fun u () String)
(assert (= u (str.replace_re (str.++ t s) re.none r)))
(push)
(assert (= t (str.replace_re (str.++ t s) re.none r)))
(push)
(check-sat)
