(set-logic QF_BV)
(set-option :incremental true)

(declare-const x (_ BitVec 32))
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(declare-const new_x (_ BitVec 32))
(declare-const new_x_ (_ BitVec 32))

(echo "Assert the assumption.")
(assert (or (= x a) (= x b)))

(echo "Asserting assignment to cvc5.")
(assert (= new_x (ite (= x a) b a)))

(echo "Pushing a new context.")
(push 1)

(echo "Asserting another assignment to cvc5.")
(assert (= new_x_ (bvxor a b x)))

(echo "Check entailment assuming new_x = new_x_.")
(echo "UNSAT (of negation) == ENTAILED")
(check-sat-assuming ((not (= new_x new_x_))))
(echo "Popping context.")
(pop 1)

(echo "Asserting another assignment to cvc5.")
(assert (= new_x_ (bvsub (bvadd a b) x)))

(echo "Check entailment assuming new_x = new_x_.")
(echo "UNSAT (of negation) == ENTAILED")
(check-sat-assuming ((not (= new_x new_x_))))

(echo "Check entailment assuming [new_x = new_x_, x != x.")
(echo "UNSAT (of negation) == ENTAILED")
(check-sat-assuming ((not (= new_x new_x_)) (not (= x x))))

(echo "Assert that a is odd, i.e. lsb is one.")
(assert (= ((_ extract 0 0) a) (_ bv1 1)))
(echo "Check satisfiability, expecting sat.")
(check-sat)
