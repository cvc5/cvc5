; COMMAND-LINE: --strings-exp --strings-fmf
; EXPECT: sat
(set-logic ALL)
(declare-fun _substvar_140_ () String)
(declare-fun _substvar_195_ () Int)
(declare-fun _substvar_201_ () Int)
(assert (let ((_let_0 (str.substr _substvar_140_ 10 (+ 0 (str.len _substvar_140_))))) (let ((_let_3 (str.substr _let_0 0 (str.indexof _let_0 "/" 0)))) (let ((_let_4 (str.substr _let_3 0 7))) (let ((_let_5 (str.substr _let_3 8 (+ _substvar_201_ (str.len _let_3)))))
  (and
    (str.contains _substvar_140_ "://")
    (str.contains _let_3 "@")
    (str.contains _let_5 ",")
    (not (= (str.len (str.substr _let_0 (+ 1 (str.indexof _let_0 "/" 0)) _substvar_195_)) 0))
    (not (= (str.len _let_4) 0))
    (not (str.contains _let_0 ".sock"))
    (not (str.contains _let_4 "@"))
    (not (= (str.len _let_5) 0))
    (= "mongodb://" (str.substr _substvar_140_ 0 10))))))))
(check-sat)

