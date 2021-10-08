; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((RightistTree 1)) ((par (T)((node (left Bool) (right (RightistTree T))) (leaf (data T))))))
(declare-fun x () (RightistTree Int))
(assert (not (= x (leaf 0))))
(check-sat)
