; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((tree 0)) (((node (left tree) (right tree)) (leaf))))
(declare-fun x () tree)
(declare-fun z () tree)
(check-sat-assuming ( (not (not (and (and (= (left (left (left (left (left (left (left (left (left (left z)))))))))) x) ((_ is node) z)) (= z x)))) ))
