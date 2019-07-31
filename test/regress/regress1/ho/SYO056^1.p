% COMMAND-LINE:  --uf-ho --finite-model-find
% EXPECT: % SZS status CounterSatisfiable for SYO056^1

%------------------------------------------------------------------------------
% File     : SYO056^1 : TPTP v7.2.0. Released v4.0.0.
% Domain   : Logic Calculi (Quantified multimodal logic)
% Problem  : Simple textbook example 13
% Version  : [Ben09] axioms.
% English  :

% Refs     : [Gol92] Goldblatt (1992), Logics of Time and Computation
%          : [Ben09] Benzmueller (2009), Email to Geoff Sutcliffe
% Source   : [Ben09]
% Names    : ex13.p [Ben09]

% Status   : CounterSatisfiable
% Rating   : 0.25 v7.2.0, 0.33 v6.4.0, 0.00 v6.3.0, 0.33 v5.4.0, 0.00 v5.0.0, 0.67 v4.1.0, 0.50 v4.0.0
% Syntax   : Number of formulae    :   64 (   0 unit;  32 type;  31 defn)
%            Number of atoms       :  238 (  36 equality; 137 variable)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :  138 (   4   ~;   4   |;   8   &; 114   @)
%                                         (   0 <=>;   8  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :  172 ( 172   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   36 (  32   :;   0   =)
%            Number of variables   :   87 (   3 sgn;  30   !;   6   ?;  51   ^)
%                                         (  87   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_CSA_EQU_NAR

% Comments :
%------------------------------------------------------------------------------
%----Include embedding of quantified multimodal logic in simple type theory
%% include('Axioms/LCL013^0.ax').
%------------------------------------------------------------------------------
thf(mvalid_type,type,(
    mvalid: ( $i > $o ) > $o )).

thf(mvalid,definition,
    ( mvalid
    = ( ^ [Phi: $i > $o] :
        ! [W: $i] :
          ( Phi @ W ) ) )).


thf(mforall_prop_type,type,(
    mforall_prop: ( ( $i > $o ) > $i > $o ) > $i > $o )).

thf(mforall_prop,definition,
    ( mforall_prop
    = ( ^ [Phi: ( $i > $o ) > $i > $o,W: $i] :
        ! [P: $i > $o] :
          ( Phi @ P @ W ) ) )).

thf(mnot_type,type,(
    mnot: ( $i > $o ) > $i > $o )).

thf(mnot,definition,
    ( mnot
    = ( ^ [Phi: $i > $o,W: $i] :
          ~ ( Phi @ W ) ) )).

thf(mor_type,type,(
    mor: ( $i > $o ) > ( $i > $o ) > $i > $o )).

thf(mor,definition,
    ( mor
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Phi @ W )
          | ( Psi @ W ) ) ) )).

thf(mimplies_type,type,(
    mimplies: ( $i > $o ) > ( $i > $o ) > $i > $o )).

thf(mimplies,definition,
    ( mimplies
    = ( ^ [Phi: $i > $o,Psi: $i > $o] :
          ( mor @ ( mnot @ Phi ) @ Psi ) ) )).

thf(mbox_type,type,(
    mbox: ( $i > $i > $o ) > ( $i > $o ) > $i > $o )).

thf(mbox,definition,
    ( mbox
    = ( ^ [R: $i > $i > $o,Phi: $i > $o,W: $i] :
        ! [V: $i] :
          ( ~ ( R @ W @ V )
          | ( Phi @ V ) ) ) )).


thf(conj,conjecture,(
    ! [R: $i > $i > $o] :
      ( mvalid
      @ ( mforall_prop
        @ ^ [A: $i > $o] :
            ( mforall_prop
            @ ^ [B: $i > $o] :
                ( mimplies @ ( mbox @ R @ ( mor @ A @ B ) ) @ ( mor @ ( mbox @ R @ A ) @ ( mbox @ R @ B ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
