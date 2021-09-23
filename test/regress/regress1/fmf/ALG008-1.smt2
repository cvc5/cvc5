; COMMAND-LINE: --finite-model-find
; COMMAND-LINE: --finite-model-find --sort-inference
; EXPECT: sat
;%--------------------------------------------------------------------------
;% File     : ALG008-1 : TPTP v5.4.0. Released v2.2.0.
;% Domain   : General Algebra
;% Problem  : TC + right identity does not give RC.
;% Version  : [MP96] (equality) axioms : Especial.
;% English  : An algebra with a right identity satisfying the Thomsen
;%            Closure (RC) condition does not necessarily satisfy the
;%            Reidemeister Closure (RC) condition.

;% Refs     : [McC98] McCune (1998), Email to G. Sutcliffe
;%          : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq
;% Source   : [McC98]
;% Names    : TC-3 [MP96]

;% Status   : Satisfiable
;% Rating   : 0.50 v5.4.0, 0.80 v5.3.0, 0.78 v5.2.0, 0.80 v5.0.0, 0.78 v4.1.0, 0.71 v4.0.1, 0.80 v4.0.0, 0.50 v3.7.0, 0.33 v3.4.0, 0.50 v3.3.0, 0.33 v3.2.0, 0.80 v3.1.0, 0.67 v2.7.0, 0.33 v2.6.0, 0.86 v2.5.0, 0.50 v2.4.0, 0.67 v2.3.0, 1.00 v2.2.1
;% Syntax   : Number of clauses     :    6 (   0 non-Horn;   5 unit;   5 RR)
;%            Number of atoms       :   10 (  10 equality)
;%            Maximal clause size   :    5 (   2 average)
;%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
;%            Number of functors    :    9 (   8 constant; 0-2 arity)
;%            Number of variables   :    9 (   0 singleton)
;%            Maximal term depth    :    2 (   2 average)
;% SPC      : CNF_SAT_RFO_EQU_NUE

;% Comments : The smallest model has 3 elements.
;%--------------------------------------------------------------------------
;%----Thomsen Closure (TC) condition:
(set-logic UF)
(set-info :status sat)
(declare-sort sort__smt2 0)
; functions
(declare-fun multiply__smt2_2 ( sort__smt2 sort__smt2 ) sort__smt2)
(declare-fun identity__smt2_0 ( ) sort__smt2)
(declare-fun c4__smt2_0 ( ) sort__smt2)
(declare-fun a__smt2_0 ( ) sort__smt2)
(declare-fun c3__smt2_0 ( ) sort__smt2)
(declare-fun b__smt2_0 ( ) sort__smt2)
(declare-fun c2__smt2_0 ( ) sort__smt2)
(declare-fun c1__smt2_0 ( ) sort__smt2)
(declare-fun f__smt2_0 ( ) sort__smt2)
; predicates

; thomsen_closure axiom
(assert (forall ((?V7 sort__smt2) (?V6 sort__smt2) (?W sort__smt2) (?V sort__smt2) (?U sort__smt2) (?Z sort__smt2) (?Y sort__smt2) (?X sort__smt2)) 
    (or (not (= (multiply__smt2_2 ?X ?Y) ?Z))
        (not (= (multiply__smt2_2 ?U ?V) ?Z))
        (not (= (multiply__smt2_2 ?X ?W) ?V6))
        (not (= (multiply__smt2_2 ?V7 ?V) ?V6))
        (= (multiply__smt2_2 ?U ?W) (multiply__smt2_2 ?V7 ?Y)))) )

;%----Right identity:
; right_identity axiom
(assert (forall ((?X sort__smt2)) (= (multiply__smt2_2 ?X identity__smt2_0) ?X)) )

;%----Denial of Reidimeister Closure (RC) condidition.
; prove_reidimeister1 negated_conjecture
(assert (= (multiply__smt2_2 c4__smt2_0 a__smt2_0) (multiply__smt2_2 c3__smt2_0 b__smt2_0)) )

; prove_reidimeister2 negated_conjecture
(assert (= (multiply__smt2_2 c2__smt2_0 a__smt2_0) (multiply__smt2_2 c1__smt2_0 b__smt2_0)) )

; prove_reidimeister3 negated_conjecture
(assert (= (multiply__smt2_2 c4__smt2_0 f__smt2_0) (multiply__smt2_2 c3__smt2_0 identity__smt2_0)) )

; prove_reidimeister4 negated_conjecture
(assert (not (= (multiply__smt2_2 c2__smt2_0 f__smt2_0) (multiply__smt2_2 c1__smt2_0 identity__smt2_0))) )


(check-sat)
