; COMMAND-LINE: --finite-model-find
; EXPECT: unsat

(set-option :incremental false)
(set-logic HO_ALL)
(declare-sort $$unsorted 0)
(declare-sort nat 0)
(declare-fun x () nat)
(declare-fun n_1 () nat)
(assert (not (= x n_1)))
(declare-fun suc (nat) nat)
(declare-fun some ((-> nat Bool)) Bool)
(assert (forall ((Xx nat) (Xy nat)) (=> (= (suc Xx) (suc Xy)) (= Xx Xy)) ))
(assert (forall ((Xx nat)) (=> (not (= Xx n_1)) (some (lambda ((Xu nat)) (= Xx (suc Xu))))) ))
(assert (not (not (=> (forall ((Xx_0 nat) (Xy nat)) (=> (= x (suc Xx_0)) (=> (= x (suc Xy)) (= Xx_0 Xy))) ) (not (some (lambda ((Xu nat)) (= x (suc Xu)))))))))
(set-info :filename "NUM638^1")
(check-sat-assuming ( (not false) ))
