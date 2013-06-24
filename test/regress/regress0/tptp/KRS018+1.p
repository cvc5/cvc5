%------------------------------------------------------------------------------
% File     : KRS018+1 : TPTP v5.5.0. Released v3.1.0.
% Domain   : Knowledge Representation (Semantic Web)
% Problem  : Nothing can be defined using OWL Lite restrictions
% Version  : Especial.
% English  :

% Refs     : [Bec03] Bechhofer (2003), Email to G. Sutcliffe
%          : [TR+04] Tsarkov et al. (2004), Using Vampire to Reason with OW
% Source   : [Bec03]
% Names    : consistent_I5.2-Manifest001 [Bec03]

% Status   : Satisfiable
% Rating   : 0.00 v4.1.0, 0.25 v4.0.1, 0.00 v3.1.0
% Syntax   : Number of formulae    :    4 (   0 unit)
%            Number of atoms       :    8 (   0 equality)
%            Maximal formula depth :    5 (   4 average)
%            Number of connectives :    7 (   3 ~  ;   0  |;   1  &)
%                                         (   1 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :    6 (   0 singleton;   4 !;   2 ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_SAT_RFO_NEQ

% Comments : Sean Bechhofer says there are some errors in the encoding of
%            datatypes, so this problem may not be perfect. At least it's
%            still representative of the type of reasoning required for OWL.
%------------------------------------------------------------------------------
%----Thing and Nothing
fof(axiom_0,axiom,
    ( ! [X] :
        ( cowlThing(X)
        & ~ cowlNothing(X) ) )).

%----String and Integer disjoint
fof(axiom_1,axiom,
    ( ! [X] :
        ( xsd_string(X)
      <=> ~ xsd_integer(X) ) )).

%----Super cNothing
fof(axiom_2,axiom,
    ( ! [X] :
        ( cNothing(X)
       => ~ ( ? [Y] : rp(X,Y) ) ) )).

%----Super cNothing
fof(axiom_3,axiom,
    ( ! [X] :
        ( cNothing(X)
       => ? [Y0] : rp(X,Y0) ) )).

%------------------------------------------------------------------------------
