; COMMAND-LINE: --no-strings-lazy-pp -i
; EXPECT: unsat
(set-logic QF_S)
(declare-fun _substvar_18_ () String)
(set-option :strings-lazy-pp false)
(declare-fun str2 () String)
(declare-fun str3 () String)
(declare-fun str9 () String)
(declare-fun str10 () String)
(assert (not (str.prefixof str3 str9)))
(push 1)
(assert (= str3 str2 str10 str9 _substvar_18_))
(check-sat)
