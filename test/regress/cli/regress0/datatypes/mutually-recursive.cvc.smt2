; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((nat 0)(nat2 0)) (((succ (pred nat2)) (zero))((succ2 (pred2 nat)) (zero2))))
(declare-fun x () nat)
(declare-datatypes ((list 0)(tree 0)) (((cons (car tree) (cdr list)) (nil))((node (left tree) (right tree)) (leaf (data list)))))
(declare-fun y () tree)
(check-sat-assuming ( (not (let ((_let_1 (data y))) (let ((_let_2 (pred x))) (and (=> ((_ is succ) x) (or ((_ is zero2) _let_2) ((_ is succ2) _let_2))) (=> ((_ is leaf) y) (or ((_ is cons) _let_1) ((_ is nil) _let_1))))))) ))
