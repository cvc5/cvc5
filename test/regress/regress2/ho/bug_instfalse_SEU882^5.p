% COMMAND-LINE:  --uf-ho --full-saturate-quant --ho-elim
% EXPECT: % SZS status Theorem for bug_instfalse_SEU882^5

%------------------------------------------------------------------------------
% File     : SEU882^5 : TPTP v7.2.0. Released v4.0.0.
% Domain   : Set Theory
% Problem  : TPS problem THM139
% Version  : Especial.
% English  : Every object is in the range of some function.

% Refs     : [Bro09] Brown (2009), Email to Geoff Sutcliffe
% Source   : [Bro09]
% Names    : tps_0037 [Bro09]
%          : THM139 [TPS]

% Status   : Theorem
% Rating   : 0.11 v7.2.0, 0.00 v7.1.0, 0.12 v7.0.0, 0.14 v6.4.0, 0.17 v6.3.0, 0.20 v6.2.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v5.3.0, 0.40 v5.2.0, 0.20 v4.1.0, 0.00 v4.0.0
% Syntax   : Number of formulae    :    1 (   0 unit;   0 type;   0 defn)
%            Number of atoms       :    4 (   1 equality;   3 variable)
%            Maximal formula depth :    6 (   6 average)
%            Number of connectives :    1 (   0   ~;   0   |;   0   &;   1   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    1 (   1   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    1 (   0   :;   0   =)
%            Number of variables   :    3 (   0 sgn;   1   !;   2   ?;   0   ^)
%                                         (   3   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU_NAR

% Comments : This problem is from the TPS library. Copyright (c) 2009 The TPS
%            project in the Department of Mathematical Sciences at Carnegie
%            Mellon University. Distributed under the Creative Commons copyleft
%            license: http://creativecommons.org/licenses/by-sa/3.0/
%          : Polymorphic definitions expanded.
%          :
%------------------------------------------------------------------------------
thf(cTHM139_pme,conjecture,(
    ! [Xy: $i] :
    ? [Xf: $i > $i,Xx: $i] :
      ( ( Xf @ Xx )
      = Xy ) )).

%------------------------------------------------------------------------------
