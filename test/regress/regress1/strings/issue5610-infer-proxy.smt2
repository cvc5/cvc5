; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(declare-fun str5 () String)
(declare-fun str6 () String)
(declare-fun str10 () String)
(declare-fun str11 () String)
(assert (not (= str6 str5)))
(assert (xor true true true (distinct "" str6 (str.++ (str.from_int (str.len (str.++ str10 str11))) (str.++ str11 "tCEuUoROixKOUo" "wuPPPbRfGeDdhIafLoGcubFWViLfPaiooaekchLBSfgSaprsJijOvY"))) (str.prefixof (str.++ "tCEuUoROixKOUo" "wuPPPbRfGeDdhIafLoGcubFWViLfPaiooaekchLBSfgSaprsJijOvY") (str.++ str5 (str.++ (str.from_int (str.len (str.++ str10 str11))) (str.++ "tCEuUoROixKOUo" "wuPPPbRfGeDdhIafLoGcubFWViLfPaiooaekchLBSfgSaprsJijOvY"))))))
(check-sat)
