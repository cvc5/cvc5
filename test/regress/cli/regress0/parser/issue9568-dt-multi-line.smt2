; EXPECT: sat
(set-logic ALL)

(declare-datatype T
  ((T (T_id String)))
)

(check-sat)
