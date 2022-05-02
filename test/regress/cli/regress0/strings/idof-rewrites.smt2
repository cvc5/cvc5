(set-logic ALL)
(set-info :status sat)
(set-option :strings-exp true)
(declare-fun s () String)
(declare-fun t () String)

; all of these should rewrite to true
(assert (= (str.indexof (str.++ s "abc") "ab" 0) (str.indexof (str.++ s "ab") "ab" 0)))
(assert (= (str.indexof (str.++ s "abc" t "a") t 2) (str.indexof (str.++ s "abc" t "c") t 2)))
(assert (= (str.indexof (str.++ "ddd" s "abc") "ab" 2) (+ 1 (str.indexof (str.++ "ed" s "ab") "ab" 1))))
(assert (= (str.indexof (str.++ "dd" s "dd") "ab" 0) (str.indexof (str.++ "dd" s "ee") "ab" 0)))
(assert (= (str.indexof (str.++ "dd" s "dabd") "ab" 1) (+ 2 (str.indexof (str.++ s "dab" t) "ab" 0))))
(check-sat)