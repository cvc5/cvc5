; COMMAND-LINE:
; EXPECT: unsat
;; repeated assumption in local proof lead to confusion with
;; discharge. Disabling for now while the use of "discharge" is not
;; properly defined in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun a () String)
(assert
 (= (str.++ a "0" (str.at (str.substr (str.++ a a a) 0 3) (str.len a)) "A")
  (str.++ "0" (str.from_code (str.len a)) (str.replace "AA" (str.++ a "AA") a))))
(check-sat)
