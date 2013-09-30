%--------------------------------------------------------------------------
% File     : MGT019+2 : TPTP v5.5.0. Released v2.0.0.
% Domain   : Management (Organisation Theory)
% Problem  : Growth rate of EPs exceeds that of FMs in stable environments
% Version  : [PM93] axioms.
% English  : The growth rate of efficent producers exceeds the growth rate
%            of first movers past a certain time in stable environments.

% Refs     : [PM93]  Peli & Masuch (1993), The Logic of Propogation Strateg
%          : [PM94]  Peli & Masuch (1994), The Logic of Propogation Strateg
%          : [PB+94] Peli et al. (1994), A Logical Approach to Formalizing
% Source   : [PM93]
% Names    : LEMMA 1 [PM93]
%          : L1 [PB+94]

% Status   : CounterSatisfiable
% Rating   : 0.00 v4.1.0, 0.20 v4.0.1, 0.00 v3.5.0, 0.33 v3.4.0, 0.00 v2.1.0
% Syntax   : Number of formulae    :    5 (   0 unit)
%            Number of atoms       :   21 (   1 equality)
%            Maximal formula depth :    8 (   6 average)
%            Number of connectives :   17 (   1 ~  ;   1  |;   8  &)
%                                         (   0 <=>;   7 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    7 (   0 propositional; 1-4 arity)
%            Number of functors    :    5 (   2 constant; 0-2 arity)
%            Number of variables   :   11 (   0 singleton;   9 !;   2 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_CSA_RFO_SEQ

% Comments : There is no MGT019+1 as Kamps did not send it to me.
%--------------------------------------------------------------------------
%----Subsitution axioms
%----Problem axioms
%----L2. The disbanding rate of first movers exceeds the disbanding
%----rate of efficient producers.
fof(l2,axiom,
    ( ~ ( ! [E,T] :
            ( ( environment(E)
              & subpopulations(first_movers,efficient_producers,E,T) )
           => greater(disbanding_rate(first_movers,T),disbanding_rate(efficient_producers,T)) ) ) )).

%----If EP have lower disbanding rate and not lower founding rate than
%----FM, then EP have higher growth rate.
fof(mp_EP_lower_disbanding_rate,axiom,
    ( ! [T] :
        ( ( greater(disbanding_rate(first_movers,T),disbanding_rate(efficient_producers,T))
          & greater_or_equal(founding_rate(efficient_producers,T),founding_rate(first_movers,T)) )
       => greater(growth_rate(efficient_producers,T),growth_rate(first_movers,T)) ) )).

%----MP. on "greater or equal to"
fof(mp_greater_or_equal,axiom,
    ( ! [X,Y] :
        ( greater_or_equal(X,Y)
       => ( greater(X,Y)
          | X = Y ) ) )).

%----A8.  The founding rate of first movers does not exceed the founding
%----rate of efficient producers past a certain point in a stable
%----environment.
fof(a8,hypothesis,
    ( ! [E] :
        ( ( environment(E)
          & stable(E) )
       => ? [To] :
            ( in_environment(E,To)
            & ! [T] :
                ( ( subpopulations(first_movers,efficient_producers,E,T)
                  & greater_or_equal(T,To) )
               => greater_or_equal(founding_rate(efficient_producers,T),founding_rate(first_movers,T)) ) ) ) )).

%----GOAL: L1. The growth rate of efficient producers exceeds the growth
%----rate of first movers past a certain time in stable environments.
fof(prove_l1,conjecture,
    ( ! [E] :
        ( ( environment(E)
          & stable(E) )
       => ? [To] :
            ( in_environment(E,To)
            & ! [T] :
                ( ( subpopulations(first_movers,efficient_producers,E,T)
                  & greater_or_equal(T,To) )
               => greater(growth_rate(efficient_producers,T),growth_rate(first_movers,T)) ) ) ) )).

%--------------------------------------------------------------------------
