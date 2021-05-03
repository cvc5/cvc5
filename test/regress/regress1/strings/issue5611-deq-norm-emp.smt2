; COMMAND-LINE: -i --strings-exp
; EXPECT: sat
(set-logic ALL)
(declare-fun str7 () String)
(declare-fun str8 () String)
(declare-fun str9 () String)
(assert (not (= str8 (str.replace_re_all (str.++ str9 str8 str7) (str.to_re "ULfQhzdcQSfqWSXyjuptqjqsazpyjzdDddlJPLDJhalmhBhlNBKZvoxoLOpfplkqhvIRHMOMDAGIdoRyiZmxmMvRijgpFnd") str9))))
(push)
(assert (and (str.in_re str8 (str.to_re str7)) (not (= str9 (str.replace_re_all (str.++ str8 str8) (str.to_re "ULfQhzdcQSfqWSXyjuptqjqsazpyjzdDddlJPLDJhalmhBhlNBKZvoxoLOpfplkqhvIRHMOMDAGIdoRyiZmxmMvRijgpFnd") str9)))))
(check-sat)
