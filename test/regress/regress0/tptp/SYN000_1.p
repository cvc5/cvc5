%------------------------------------------------------------------------------
% File     : SYN000_1 : TPTP v5.5.0. Released v5.0.0.
% Domain   : Syntactic
% Problem  : Basic TPTP TFF syntax without arithmetic
% Version  : Biased.
% English  : Basic TPTP TFF syntax that you can't survive without parsing.

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Theorem
% Rating   : 0.40 v5.5.0, 0.25 v5.4.0, 0.33 v5.2.0, 0.67 v5.0.0
% Syntax   : Number of formulae    :   38 (  21 unit;  25 type)
%            Number of atoms       :   74 (   3 equality)
%            Maximal formula depth :    7 (   3 average)
%            Number of connectives :   28 (   9   ~;  10   |;   3   &)
%                                         (   1 <=>;   3  =>;   1  <=;   1 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :   17 (  10   >;   7   *;   0   +;   0  <<)
%            Number of predicates  :   37 (  30 propositional; 0-3 arity)
%            Number of functors    :   10 (   6 constant; 0-3 arity)
%            Number of variables   :   14 (   1 sgn;   6   !;   8   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : TFF_THM_EQU_NAR

% Comments :
%------------------------------------------------------------------------------
%----Propositional
tff(p0_type,type,(
    p0: $o )).

tff(q0_type,type,(
    q0: $o )).

tff(r0_type,type,(
    r0: $o )).

tff(s0_type,type,(
    s0: $o )).

tff(propositional,axiom,
    ( ( p0
      & ~ q0 )
   => ( r0
      | ~ s0 ) )).

%----First-order
tff(a_type,type,(
    a: $i )).

tff(b_type,type,(
    b: $i )).

tff(h_type,type,(
    h: $i )).

tff(f_type,type,(
    f: $i > $i )).

tff(g_type,type,(
    g: ( $i * $i * $i ) > $i )).

tff(p_type,type,(
    p: $i > $o )).

tff(q_type,type,(
    q: ( $i * $i ) > $o )).

tff(r_type,type,(
    r: ( $i * $i * $i ) > $o )).

tff(s_type,type,(
    s: $i > $o )).

tff(first_order,axiom,(
    ! [X: $i] :
      ( ( p(X)
        | ~ q(X,a) )
     => ? [Y: $i,Z: $i] :
          ( r(X,f(Y),g(X,f(Y),Z))
          & ~ s(f(f(f(b)))) ) ) )).

%----Equality
tff(equality,axiom,(
    ? [Y: $i] :
    ! [X: $i,Z: $i] :
      ( f(Y) = g(X,f(Y),Z)
      | f(f(f(b))) != a
      | X = f(Y) ) )).

%----True and false
tff(true_false,axiom,
    ( $true
    | $false )).

tff(quoted_proposition_type,type,(
    'A proposition': $o )).

tff(quoted_predicate_type,type,(
    'A predicate': $i > $o )).

tff(quoted_constant_type,type,(
    'A constant': $i )).

tff(quoted_function_type,type,(
    'A function': $i > $i )).

tff(quoted_escape_type,type,(
    'A \'quoted \\ escape\'': $i )).

%----Quoted symbols
tff(single_quoted,axiom,
    ( 'A proposition'
    | 'A predicate'(a)
    | p('A constant')
    | p('A function'(a))
    | p('A \'quoted \\ escape\'') )).

%----Connectives - seen |, &, =>, ~ already
tff(useful_connectives,axiom,(
    ! [X: $i] :
      ( ( p(X)
       <= ~ q(X,a) )
    <=> ? [Y: $i,Z: $i] :
          ( r(X,f(Y),g(X,f(Y),Z))
        <~> ~ s(f(f(f(b)))) ) ) )).

%----New types
tff(new_type,type,(
    new: $tType )).

tff(newc_type,type,(
    newc: new )).

tff(newf_type,type,(
    newf: ( new * $i ) > new )).

tff(newp_type,type,(
    newp: ( new * $i ) > $o )).

tff(new_axiom,axiom,(
    ! [X: new] : newp(newf(newc,a),a) )).

%----Annotated formula names
tff(123,axiom,(
    ! [X: $i] :
      ( ( p(X)
        | ~ q(X,a) )
     => ? [Y: $i,Z: $i] :
          ( r(X,f(Y),g(X,f(Y),Z))
          & ~ s(f(f(f(b)))) ) ) )).

%----Roles
tff(role_hypothesis,hypothesis,(
    p(h) )).

tff(role_conjecture,conjecture,(
    ? [X: $i] : p(X) )).

%----Include directive
include('Axioms/SYN000_0.ax').

%----Comments
/* This
   is a block
   comment.
*/

%------------------------------------------------------------------------------
