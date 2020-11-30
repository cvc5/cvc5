% COMMAND-LINE:  --uf-ho
% EXPECT: % SZS status Unsatisfiable for bug_nodbuilding_interpreted_SYO042^1

%------------------------------------------------------------------------------
% File     : SYO042^1 : TPTP v7.2.0. Released v4.0.0.
% Domain   : Syntactic
% Problem  : Unsatisfiable basic formula 4
% Version  : Especial.
% English  :

% Refs     : [BS09a] Brown E. & Smolka (2009), Terminating Tableaux for the
%          : [BS09b] Brown E. & Smolka (2009), Extended First-Order Logic
% Source   : [BS09a]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.33 v5.3.0, 0.67 v5.0.0, 0.33 v4.1.0, 0.67 v4.0.1, 1.00 v4.0.0
% Syntax   : Number of formulae    :    5 (   0 unit;   4 type;   0 defn)
%            Number of atoms       :   15 (   3 equality;   0 variable)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   10 (   2   ~;   0   |;   4   &;   4   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    3 (   3   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    6 (   4   :;   0   =)
%            Number of variables   :    0 (   0 sgn;   0   !;   0   ?;   0   ^)
%                                         (   0   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_UNS_EQU_NAR

% Comments : The fragment of simple type theory that restricts equations to
%            base types and disallows lambda abstraction and quantification is
%            decidable. This is an example.
%------------------------------------------------------------------------------
thf(g,type,(
    g: $o > $o )).

thf(p,type,(
    p: ( $o > $o ) > $o )).

thf(x,type,(
    x: $o )).

thf(y,type,(
    y: $o )).

thf(4,axiom,
    ( ( x != y )
    & ( ( g @ x )
      = y )
    & ( ( g @ y )
      = x )
    & ( p @ g )
    & ~ ( p @ (~) ) )).

%------------------------------------------------------------------------------
