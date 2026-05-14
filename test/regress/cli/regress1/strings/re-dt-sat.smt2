; COMMAND-LINE: --re-first-class
; EXPECT: sat
(set-logic ALL)
(declare-datatype List ((cons (head RegLan) (tail List)) (nil)))
(declare-fun s () String)
(declare-fun x () Int)
(assert (= (cons (re.++ (str.to_re "A") (re.* (str.to_re "A"))) nil) (cons (re.+ (str.to_re "A")) nil)))
(check-sat)
