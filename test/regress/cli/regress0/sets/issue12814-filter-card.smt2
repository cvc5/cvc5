; COMMAND-LINE: --check-models-unknown --produce-models
; EXPECT: unknown
(set-logic HO_ALL)
(set-option :sets-exp true)
(define-fun all-str ((P (-> String Bool)) (S (Set String))) Bool
  (= (set.filter P S) S))
(declare-const groups (Set String))
(assert (all-str (lambda ((x String)) (str.prefixof "foo" x)) groups))
(assert (all-str (lambda ((x String)) (str.suffixof "bar" x)) groups))
(assert (> (set.card groups) 1))
(check-sat)
