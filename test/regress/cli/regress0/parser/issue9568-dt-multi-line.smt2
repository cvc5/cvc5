; EXPECT: sat
(set-logic ALL)

(declare-datatype Td
  ((T (T_id String)))
)

(check-sat)
