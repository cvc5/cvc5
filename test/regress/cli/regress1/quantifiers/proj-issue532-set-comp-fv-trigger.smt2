; EXPECT: unknown
(set-logic ALL)
(check-sat-assuming ((forall ((x RoundingMode) (_x RoundingMode)) (set.choose (set.comprehension ((_x16 RoundingMode)) (set.is_singleton (set.singleton x)) (set.is_singleton (set.insert x _x16 (set.singleton _x))))))))
