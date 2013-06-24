%------------------------------------------------------------------------------
% File     : SYN000=2 : TPTP v5.5.0. Bugfixed v5.5.1.
% Domain   : Syntactic
% Problem  : TF0 syntax with arithmetic
% Version  : Biased.
% English  : 

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Theorem
% Rating   : ? v5.5.1
% Syntax   : Number of formulae    :   83 (  73 unit;   6 type)
%            Number of atoms       :  100 (   4 equality)
%            Maximal formula depth :    7 (   1 average)
%            Number of connectives :   14 (   0   ~;  10   |;   1   &)
%                                         (   0 <=>;   3  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    3 (   3   >;   0   *;   0   +;   0  <<)
%            Number of predicates  :   20 (  10 propositional; 0-2 arity)
%            Number of functors    :   41 (  24 constant; 0-2 arity)
%            Number of variables   :   14 (   1 sgn;   3   !;  11   ?)
%            Maximal term depth    :    3 (   1 average)
%            Arithmetic symbols    :   37 (   9 pred;    7 func;   21 numbers)
% SPC      : TF0_THM_EQU_ARI

% Comments : 
% Bugfixes : v5.5.1 - Removed $evaleq.
%------------------------------------------------------------------------------
%----Types for what follows
tff(p_int_type,type,(
    p_int: $int > $o )).

tff(p_rat_type,type,(
    p_rat: $rat > $o )).

tff(p_real_type,type,(
    p_real: $real > $o )).

tff(a_int,type,(
    a_int: $int )).

tff(a_rat,type,(
    a_rat: $rat )).

tff(a_real,type,(
    a_real: $real )).

%----Numbers
tff(integers,axiom,
    ( p_int(123)
    | p_int(-123) )).

tff(rationals,axiom,
    ( p_rat(123/456)
    | p_rat(-123/456)
    | p_rat(123/456) )).

tff(reals,axiom,
    ( p_real(123.456)
    | p_real(-123.456)
    | p_real(123.456E78)
    | p_real(123.456e78)
    | p_real(-123.456E78)
    | p_real(123.456E-78)
    | p_real(-123.456E-78) )).

%----Variables
tff(variables_int,axiom,(
    ! [X: $int] :
    ? [Y: $int] :
      ( p_int(X)
     => p_int(Y) ) )).

tff(variables_rat,axiom,(
    ! [X: $rat] :
    ? [Y: $rat] :
      ( p_rat(X)
     => p_rat(Y) ) )).

tff(variables_real,axiom,(
    ! [X: $real] :
    ? [Y: $real] :
      ( p_real(X)
     => p_real(Y) ) )).

%----Arithmetic relations
tff(less_int,axiom,(
    $less(a_int,3) )).

tff(less_rat,axiom,(
    $less(a_rat,3/9) )).

tff(less_real,axiom,(
    $less(a_real,3.3) )).

tff(lesseq_int,axiom,(
    $lesseq(a_int,3) )).

tff(lesseq_rat,axiom,(
    $lesseq(a_rat,3/9) )).

tff(lesseq_real,axiom,(
    $lesseq(a_real,3.3) )).

tff(greater_int,axiom,(
    $greater(a_int,-3) )).

tff(greater_rat,axiom,(
    $greater(a_rat,-3/9) )).

tff(greater_real,axiom,(
    $greater(a_real,-3.3) )).

tff(greatereq_int,axiom,(
    $greatereq(a_int,-3) )).

tff(greatereq_rat,axiom,(
    $greatereq(a_rat,-3/9) )).

tff(greatereq_real,axiom,(
    $greatereq(a_real,-3.3) )).

tff(equal_int,axiom,(
    a_int = 0 )).

tff(equal_rat,axiom,(
    a_rat = 0/1 )).

tff(equal_real,axiom,(
    a_real = 0.0 )).

%----Arithmetic functions
tff(uminus_int,axiom,(
    p_int($uminus(3)) )).

tff(uminus_rat,axiom,(
    p_rat($uminus(3/9)) )).

tff(uminus_real,axiom,(
    p_real($uminus(3.3)) )).

tff(sum_int,axiom,(
    p_int($sum(3,3)) )).

tff(sum_rat,axiom,(
    p_rat($sum(3/9,3/9)) )).

tff(sum_real,axiom,(
    p_real($sum(3.3,3.3)) )).

tff(difference_int,axiom,(
    p_int($difference(3,3)) )).

tff(difference_rat,axiom,(
    p_rat($difference(3/9,3/9)) )).

tff(difference_real,axiom,(
    p_real($difference(3.3,3.3)) )).

tff(product_int,axiom,(
    p_int($product(3,3)) )).

tff(product_rat,axiom,(
    p_rat($product(3/9,3/9)) )).

tff(product_real,axiom,(
    p_real($product(3.3,3.3)) )).

tff(quotient_rat,axiom,(
    p_rat($quotient(3/9,3/9)) )).

tff(quotient_real,axiom,(
    p_real($quotient(3.3,3.3)) )).

tff(quotient_e_int,axiom,(
    p_int($quotient_e(3,3)) )).

tff(quotient_e_rat,axiom,(
    p_rat($quotient_e(3/9,3/9)) )).

tff(quotient_e_real,axiom,(
    p_real($quotient_e(3.3,3.3)) )).

tff(quotient_t_int,axiom,(
    p_int($quotient_t(3,3)) )).

tff(quotient_t_rat,axiom,(
    p_rat($quotient_t(3/9,3/9)) )).

tff(quotient_t_real,axiom,(
    p_real($quotient_t(3.3,3.3)) )).

tff(quotient_f_int,axiom,(
    p_int($quotient_f(3,3)) )).

tff(quotient_f_rat,axiom,(
    p_rat($quotient_f(3/9,3/9)) )).

tff(quotient_f_real,axiom,(
    p_real($quotient_f(3.3,3.3)) )).

tff(remainder_e_int,axiom,(
    p_int($remainder_e(3,3)) )).

tff(remainder_e_rat,axiom,(
    p_rat($remainder_e(3/9,3/9)) )).

tff(remainder_e_real,axiom,(
    p_real($remainder_e(3.3,3.3)) )).

tff(remainder_t_int,axiom,(
    p_int($remainder_t(3,3)) )).

tff(remainder_t_rat,axiom,(
    p_rat($remainder_t(3/9,3/9)) )).

tff(remainder_t_real,axiom,(
    p_real($remainder_t(3.3,3.3)) )).

tff(remainder_f_int,axiom,(
    p_int($remainder_f(3,3)) )).

tff(remainder_f_rat,axiom,(
    p_rat($remainder_f(3/9,3/9)) )).

tff(remainder_f_real,axiom,(
    p_real($remainder_f(3.3,3.3)) )).

tff(floor_int,axiom,(
    p_int($floor(3)) )).

tff(floor_rat,axiom,(
    p_rat($floor(3/9)) )).

tff(floor_int,axiom,(
    p_real($floor(3.3)) )).

tff(ceiling_int,axiom,(
    p_int($ceiling(3)) )).

tff(ceiling_rat,axiom,(
    p_rat($ceiling(3/9)) )).

tff(ceiling_int,axiom,(
    p_real($ceiling(3.3)) )).

tff(truncate_int,axiom,(
    p_int($truncate(3)) )).

tff(truncate_rat,axiom,(
    p_rat($truncate(3/9)) )).

tff(truncate_int,axiom,(
    p_real($truncate(3.3)) )).

%----Recognizing numbers
tff(is_int_int,axiom,(
    ? [X: $int] : $is_int(X) )).

tff(is_int_rat,axiom,(
    ? [X: $rat] : $is_int(X) )).

tff(is_int_real,axiom,(
    ? [X: $real] : $is_int(X) )).

tff(is_rat_rat,axiom,(
    ? [X: $rat] : $is_rat(X) )).

tff(is_rat_real,axiom,(
    ? [X: $real] : $is_rat(X) )).

%----Coercion
tff(to_int_int,axiom,(
    p_int($to_int(3)) )).

tff(to_int_rat,axiom,(
    p_int($to_int(3/9)) )).

tff(to_int_real,axiom,(
    p_int($to_int(3.3)) )).

tff(to_rat_int,axiom,(
    p_rat($to_rat(3)) )).

tff(to_rat_rat,axiom,(
    p_rat($to_rat(3/9)) )).

tff(to_rat_real,axiom,(
    p_rat($to_rat(3.3)) )).

tff(to_real_int,axiom,(
    p_real($to_real(3)) )).

tff(to_real_rat,axiom,(
    p_real($to_real(3/9)) )).

tff(to_real_real,axiom,(
    p_real($to_real(3.3)) )).

%----A conjecture to prove
tff(mixed,conjecture,(
    ? [X: $int,Y: $rat,Z: $real] :
      ( Y = $to_rat($sum(X,2))
      & ( $less($to_int(Y),3)
        | $greater($to_real(Y),3.3) ) ) )).

%------------------------------------------------------------------------------
