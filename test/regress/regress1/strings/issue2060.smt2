(set-logic QF_S)
(set-info :status sat)

(declare-const action String)
(declare-const example_key String)

(assert (str.in.re action (re.++
                           (str.to.re "foobar:ab")
                           (re.* re.allchar)
                   )))

(declare-const action_1 String)
(declare-const action_2 String)

(assert (and
         (= action (str.++ action_1 example_key action_2))
         (= action_1 "foobar:a")
         ))

(check-sat)
