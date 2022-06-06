; EXPECT: unsat
; COMMAND-LINE: --sygus-inference --strings-exp -q
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic ALL)
(declare-fun a () String) 
(declare-fun b () String) 
(declare-fun c () String)
(declare-fun d () String)
(declare-fun f () String)
(declare-fun e () String)
(assert
  (not
    (=
      (str.contains
        c
        (str.replace d (str.substr b 0 (str.len d)) "A")
      )
      (str.contains c "A")
    )
  )
)
(assert (= a (str.++ c f)))
(assert (= b (str.++ d e)))
(check-sat) 
