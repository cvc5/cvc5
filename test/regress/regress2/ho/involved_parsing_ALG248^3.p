% COMMAND-LINE:  --uf-ho --ho-elim
% EXPECT: % SZS status Theorem for involved_parsing_ALG248^3

%------------------------------------------------------------------------------
% File     : ALG248^3 : TPTP v7.2.0. Bugfixed v5.2.0.
% Domain   : Algebra
% Problem  : Push property lemma 1
% Version  : [Bro09] axioms : Reduced > Especial.
% English  :

% Refs     : [DHK95] Dowek et al. (1995), Higher-order Unification via Expl
%          : [Zha08] Zhang (2008), Using LEO-II to Prove Properties of an E
%          : [Ben09] Benzmueller (2009), Email to Geoff Sutcliffe
%          : [Bro09] Brown (2009), M-Set Models
% Source   : [Ben09]
% Names    : pushprop_lem1v2_lthm [Ben09]

% Status   : Theorem
% Rating   : 0.11 v7.2.0, 0.00 v7.1.0, 0.25 v7.0.0, 0.14 v6.4.0, 0.17 v6.3.0, 0.20 v6.2.0, 0.00 v6.1.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v5.2.0
% Syntax   : Number of formulae    :  238 (   1 unit; 124 type; 113 defn)
%            Number of atoms       : 2372 ( 161 equality; 723 variable)
%            Maximal formula depth :   39 (   8 average)
%            Number of connectives : 1942 (   6   ~;   0   |;   4   &; 916   @)
%                                         (   2 <=>;1014  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :  128 ( 128   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :  126 ( 124   :;   0   =)
%            Number of variables   :  327 (   3 sgn; 283   !;   5   ?;  39   ^)
%                                         ( 327   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU_NAR

% Comments :
% Bugfixes : v5.2.0 - Bugfixes in ALG003^0.ax
%------------------------------------------------------------------------------
%----Include Untyped Lambda Sigma defs
%% include('Axioms/ALG003^0.ax').
%------------------------------------------------------------------------------
thf(term_type,type,(
    term: $tType )).

thf(subst_type,type,(
    subst: $tType )).

thf(one_type,type,(
    one: term )).

thf(ap_type,type,(
    ap: term > term > term )).

thf(lam_type,type,(
    lam: term > term )).

thf(sub_type,type,(
    sub: term > subst > term )).

thf(id_type,type,(
    id: subst )).

thf(sh_type,type,(
    sh: subst )).

thf(push_type,type,(
    push: term > subst > subst )).

thf(comp_type,type,(
    comp: subst > subst > subst )).

thf(var_type,type,(
    var: term > $o )).

thf(pushprop_lem1v2_type,type,(
    pushprop_lem1v2: $o )).

thf(pushprop_lem1_gthm_type,type,(
    pushprop_lem1_gthm: $o )).

thf(axmap_type,type,(
    axmap: $o )).

thf(pushprop_lem0_gthm_type,type,(
    pushprop_lem0_gthm: $o )).

thf(shinj_type,type,(
    shinj: $o )).

thf(hoasinduction_lem1v2_type,type,(
    hoasinduction_lem1v2: $o )).

thf(hoasinduction_lem1v2_gthm_type,type,(
    hoasinduction_lem1v2_gthm: $o )).

thf(hoasap_type,type,(
    hoasap: subst > term > subst > term > term )).

thf(induction2lem_type,type,(
    induction2lem: $o )).

thf(hoasinduction_lem3v2_f_type,type,(
    hoasinduction_lem3v2_f: $o )).

thf(axvarshift_type,type,(
    axvarshift: $o )).

thf(hoasapinj2_type,type,(
    hoasapinj2: $o )).

thf(hoasapnotvar_gthm_type,type,(
    hoasapnotvar_gthm: $o )).

thf(hoasapinj1_type,type,(
    hoasapinj1: $o )).

thf(ulamvar1_type,type,(
    ulamvar1: $o )).

thf(induction2lem_lthm_type,type,(
    induction2lem_lthm: $o )).

thf(hoasinduction_lem3v2_gthm_type,type,(
    hoasinduction_lem3v2_gthm: $o )).

thf(apnotvar_type,type,(
    apnotvar: $o )).

thf(pushprop_lthm_orig_type,type,(
    pushprop_lthm_orig: $o )).

thf(hoasinduction_lem3v2_f_lthm_type,type,(
    hoasinduction_lem3v2_f_lthm: $o )).

thf(hoasinduction_lthm_type,type,(
    hoasinduction_lthm: $o )).

thf(hoasinduction_no_psi_cond_lthm_type,type,(
    hoasinduction_no_psi_cond_lthm: $o )).

thf(hoaslaminj_type,type,(
    hoaslaminj: $o )).

thf(hoasinduction_lem3aaa_type,type,(
    hoasinduction_lem3aaa: $o )).

thf(induction2lem_gthm_type,type,(
    induction2lem_gthm: $o )).

thf(hoasinduction_lem3aa_lthm_type,type,(
    hoasinduction_lem3aa_lthm: $o )).

thf(hoasinduction_lem3_type,type,(
    hoasinduction_lem3: $o )).

thf(hoasinduction_lem2_type,type,(
    hoasinduction_lem2: $o )).

thf(termmset_lthm_type,type,(
    termmset_lthm: $o )).

thf(hoasinduction_lem1_type,type,(
    hoasinduction_lem1: $o )).

thf(hoaslamnotap_lthm_type,type,(
    hoaslamnotap_lthm: $o )).

thf(pushprop_lem1v2_lthm_type,type,(
    pushprop_lem1v2_lthm: $o )).

thf(hoasapnotvar_type,type,(
    hoasapnotvar: $o )).

thf(hoasinduction_lem0_type,type,(
    hoasinduction_lem0: $o )).

thf(hoasinduction_type,type,(
    hoasinduction: $o )).

thf(hoasinduction_gthm_type,type,(
    hoasinduction_gthm: $o )).

thf(axapp_type,type,(
    axapp: $o )).

thf(hoaslamnotvar_lthm_type,type,(
    hoaslamnotvar_lthm: $o )).

thf(pushprop_lem3v2_lthm_type,type,(
    pushprop_lem3v2_lthm: $o )).

thf(hoasinduction_lem3b_lthm_type,type,(
    hoasinduction_lem3b_lthm: $o )).

thf(ulamvarind_type,type,(
    ulamvarind: $o )).

thf(induction_type,type,(
    induction: $o )).

thf(hoasinduction_lem3a_lthm_type,type,(
    hoasinduction_lem3a_lthm: $o )).

thf(termmset_gthm_type,type,(
    termmset_gthm: $o )).

thf(hoasinduction_lem3aa_type,type,(
    hoasinduction_lem3aa: $o )).

thf(pushprop_lem1v2_gthm_type,type,(
    pushprop_lem1v2_gthm: $o )).

thf(hoaslamnotap_gthm_type,type,(
    hoaslamnotap_gthm: $o )).

thf(hoaslamnotvar_gthm_type,type,(
    hoaslamnotvar_gthm: $o )).

thf(hoasinduction_lem3b_gthm_type,type,(
    hoasinduction_lem3b_gthm: $o )).

thf(pushprop_lem2v2_type,type,(
    pushprop_lem2v2: $o )).

thf(hoasinduction_lem3a_gthm_type,type,(
    hoasinduction_lem3a_gthm: $o )).

thf(axclos_type,type,(
    axclos: $o )).

thf(axassoc_type,type,(
    axassoc: $o )).

thf(hoasinduction_lem2v2_type,type,(
    hoasinduction_lem2v2: $o )).

thf(pushprop_lthm_type,type,(
    pushprop_lthm: $o )).

thf(apinj2_type,type,(
    apinj2: $o )).

thf(apinj1_type,type,(
    apinj1: $o )).

thf(hoasapinj2_lthm_type,type,(
    hoasapinj2_lthm: $o )).

thf(hoasinduction_lem3v2a_type,type,(
    hoasinduction_lem3v2a: $o )).

thf(hoasapinj1_lthm_type,type,(
    hoasapinj1_lthm: $o )).

thf(hoaslaminj_lthm_type,type,(
    hoaslaminj_lthm: $o )).

thf(axvarcons_type,type,(
    axvarcons: $o )).

thf(hoaslam_type,type,(
    hoaslam: subst > ( subst > term > term ) > term )).

thf(axscons_type,type,(
    axscons: $o )).

thf(hoasinduction_lem2v2_gthm_type,type,(
    hoasinduction_lem2v2_gthm: $o )).

thf(axidr_type,type,(
    axidr: $o )).

thf(pushprop_lem1_type,type,(
    pushprop_lem1: $o )).

thf(laminj_type,type,(
    laminj: $o )).

thf(hoasinduction_lem3_lthm_type,type,(
    hoasinduction_lem3_lthm: $o )).

thf(pushprop_lem0_type,type,(
    pushprop_lem0: $o )).

thf(pushprop_gthm_type,type,(
    pushprop_gthm: $o )).

thf(axabs_type,type,(
    axabs: $o )).

thf(hoasinduction_lem3v2a_lthm_type,type,(
    hoasinduction_lem3v2a_lthm: $o )).

thf(hoasinduction_lem2_lthm_type,type,(
    hoasinduction_lem2_lthm: $o )).

thf(hoasapinj2_gthm_type,type,(
    hoasapinj2_gthm: $o )).

thf(hoasinduction_p_and_p_prime_type,type,(
    hoasinduction_p_and_p_prime: ( subst > term > subst > $o ) > ( term > $o ) > $o )).

thf(hoasinduction_lem1_lthm_type,type,(
    hoasinduction_lem1_lthm: $o )).

thf(lamnotap_type,type,(
    lamnotap: $o )).

thf(hoasapinj1_gthm_type,type,(
    hoasapinj1_gthm: $o )).

thf(hoaslamnotvar_type,type,(
    hoaslamnotvar: $o )).

thf(axidl_type,type,(
    axidl: $o )).

thf(hoaslaminj_gthm_type,type,(
    hoaslaminj_gthm: $o )).

thf(induction2_lthm_type,type,(
    induction2_lthm: $o )).

thf(hoasinduction_lem0_lthm_type,type,(
    hoasinduction_lem0_lthm: $o )).

thf(substmonoid_lthm_type,type,(
    substmonoid_lthm: $o )).

thf(pushprop_type,type,(
    pushprop: $o )).

thf(hoasinduction_lem3_gthm_type,type,(
    hoasinduction_lem3_gthm: $o )).

thf(hoasinduction_lem2_gthm_type,type,(
    hoasinduction_lem2_gthm: $o )).

thf(hoasinduction_lem3b_type,type,(
    hoasinduction_lem3b: $o )).

thf(substmonoid_type,type,(
    substmonoid: $o )).

thf(lamnotvar_type,type,(
    lamnotvar: $o )).

thf(hoasinduction_lem3a_type,type,(
    hoasinduction_lem3a: $o )).

thf(hoasinduction_lem1_gthm_type,type,(
    hoasinduction_lem1_gthm: $o )).

thf(hoasinduction_no_psi_cond_type,type,(
    hoasinduction_no_psi_cond: $o )).

thf(induction2_gthm_type,type,(
    induction2_gthm: $o )).

thf(pushprop_lem2v2_lthm_type,type,(
    pushprop_lem2v2_lthm: $o )).

thf(hoasvar_type,type,(
    hoasvar: subst > term > subst > $o )).

thf(hoaslamnotap_type,type,(
    hoaslamnotap: $o )).

thf(substmonoid_gthm_type,type,(
    substmonoid_gthm: $o )).

thf(ulamvarsh_type,type,(
    ulamvarsh: $o )).

thf(induction2_type,type,(
    induction2: $o )).

thf(pushprop_lem3v2_type,type,(
    pushprop_lem3v2: $o )).

thf(pushprop_lem2v2_gthm_type,type,(
    pushprop_lem2v2_gthm: $o )).

thf(pushprop_lem1_lthm_type,type,(
    pushprop_lem1_lthm: $o )).

thf(hoasinduction_lem3v2_type,type,(
    hoasinduction_lem3v2: $o )).

thf(axshiftcons_type,type,(
    axshiftcons: $o )).

thf(termmset_type,type,(
    termmset: $o )).

thf(pushprop_lem0_lthm_type,type,(
    pushprop_lem0_lthm: $o )).

thf(hoasapnotvar_lthm_type,type,(
    hoasapnotvar_lthm: $o )).

thf(hoasinduction_lem3v2_lthm_type,type,(
    hoasinduction_lem3v2_lthm: $o )).

thf(pushprop_p_and_p_prime_type,type,(
    pushprop_p_and_p_prime: term > subst > ( term > $o ) > ( term > $o ) > $o )).

thf(axvarid_type,type,(
    axvarid: $o )).

thf(hoasinduction_lthm_3_type,type,(
    hoasinduction_lthm_3: $o )).

thf(axapp,definition,
    ( axapp
    = ( ! [A: term,B: term,M: subst] :
          ( ( sub @ ( ap @ A @ B ) @ M )
          = ( ap @ ( sub @ A @ M ) @ ( sub @ B @ M ) ) ) ) )).

thf(axvarcons,definition,
    ( axvarcons
    = ( ! [A: term,M: subst] :
          ( ( sub @ one @ ( push @ A @ M ) )
          = A ) ) )).

thf(axvarid,definition,
    ( axvarid
    = ( ! [A: term] :
          ( ( sub @ A @ id )
          = A ) ) )).

thf(axabs,definition,
    ( axabs
    = ( ! [A: term,M: subst] :
          ( ( sub @ ( lam @ A ) @ M )
          = ( lam @ ( sub @ A @ ( push @ one @ ( comp @ M @ sh ) ) ) ) ) ) )).

thf(axclos,definition,
    ( axclos
    = ( ! [A: term,M: subst,N: subst] :
          ( ( sub @ ( sub @ A @ M ) @ N )
          = ( sub @ A @ ( comp @ M @ N ) ) ) ) )).

thf(axidl,definition,
    ( axidl
    = ( ! [M: subst] :
          ( ( comp @ id @ M )
          = M ) ) )).

thf(axshiftcons,definition,
    ( axshiftcons
    = ( ! [A: term,M: subst] :
          ( ( comp @ sh @ ( push @ A @ M ) )
          = M ) ) )).

thf(axassoc,definition,
    ( axassoc
    = ( ! [M: subst,N: subst,K: subst] :
          ( ( comp @ ( comp @ M @ N ) @ K )
          = ( comp @ M @ ( comp @ N @ K ) ) ) ) )).

thf(axmap,definition,
    ( axmap
    = ( ! [A: term,M: subst,N: subst] :
          ( ( comp @ ( push @ A @ M ) @ N )
          = ( push @ ( sub @ A @ N ) @ ( comp @ M @ N ) ) ) ) )).

thf(axidr,definition,
    ( axidr
    = ( ! [M: subst] :
          ( ( comp @ M @ id )
          = M ) ) )).

thf(axvarshift,definition,
    ( axvarshift
    = ( ( push @ one @ sh )
      = id ) )).

thf(axscons,definition,
    ( axscons
    = ( ! [M: subst] :
          ( ( push @ ( sub @ one @ M ) @ ( comp @ sh @ M ) )
          = M ) ) )).

thf(ulamvar1,definition,
    ( ulamvar1
    = ( var @ one ) )).

thf(ulamvarsh,definition,
    ( ulamvarsh
    = ( ! [A: term] :
          ( ( var @ A )
         => ( var @ ( sub @ A @ sh ) ) ) ) )).

thf(ulamvarind,definition,
    ( ulamvarind
    = ( ! [P: term > $o] :
          ( ( P @ one )
         => ( ! [A: term] :
                ( ( var @ A )
               => ( ( P @ A )
                 => ( P @ ( sub @ A @ sh ) ) ) )
           => ! [A: term] :
                ( ( var @ A )
               => ( P @ A ) ) ) ) ) )).

thf(apinj1,definition,
    ( apinj1
    = ( ! [A: term,B: term,C: term,D: term] :
          ( ( ( ap @ A @ C )
            = ( ap @ B @ D ) )
         => ( A = B ) ) ) )).

thf(apinj2,definition,
    ( apinj2
    = ( ! [A: term,B: term,C: term,D: term] :
          ( ( ( ap @ A @ C )
            = ( ap @ B @ D ) )
         => ( C = D ) ) ) )).

thf(laminj,definition,
    ( laminj
    = ( ! [A: term,B: term] :
          ( ( ( lam @ A )
            = ( lam @ B ) )
         => ( A = B ) ) ) )).

thf(shinj,definition,
    ( shinj
    = ( ! [A: term,B: term] :
          ( ( ( sub @ A @ sh )
            = ( sub @ B @ sh ) )
         => ( A = B ) ) ) )).

thf(lamnotap,definition,
    ( lamnotap
    = ( ! [A: term,B: term,C: term] :
          ( ( lam @ A )
         != ( ap @ B @ C ) ) ) )).

thf(apnotvar,definition,
    ( apnotvar
    = ( ! [A: term,B: term] :
          ~ ( var @ ( ap @ A @ B ) ) ) )).

thf(lamnotvar,definition,
    ( lamnotvar
    = ( ! [A: term] :
          ~ ( var @ ( lam @ A ) ) ) )).

thf(induction,definition,
    ( induction
    = ( ! [P: term > $o] :
          ( ! [A: term] :
              ( ( var @ A )
             => ( P @ A ) )
         => ( ! [A: term,B: term] :
                ( ( P @ A )
               => ( ( P @ B )
                 => ( P @ ( ap @ A @ B ) ) ) )
           => ( ! [A: term] :
                  ( ( P @ A )
                 => ( P @ ( lam @ A ) ) )
             => ! [A: term] :
                  ( P @ A ) ) ) ) ) )).

thf(pushprop_p_and_p_prime,definition,
    ( pushprop_p_and_p_prime
    = ( ^ [A: term,M: subst,P: term > $o,Q: term > $o] :
        ! [X: term] :
          ( ( Q @ X )
        <=> ( P @ ( sub @ X @ ( push @ A @ M ) ) ) ) ) )).

thf(pushprop_lem0,definition,
    ( pushprop_lem0
    = ( ! [P: term > $o,A: term,M: subst] :
        ? [Q: term > $o] :
          ( pushprop_p_and_p_prime @ A @ M @ P @ Q ) ) )).

thf(pushprop_lem0_gthm,definition,
    ( pushprop_lem0_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => pushprop_lem0 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(pushprop_lem0_lthm,definition,(
    pushprop_lem0_lthm = pushprop_lem0 )).

thf(pushprop_lem1,definition,
    ( pushprop_lem1
    = ( ! [P: term > $o,K: term > $o,A: term,M: subst,B: term] :
          ( ( P @ A )
         => ( K @ ( sub @ A @ ( push @ B @ M ) ) ) ) ) )).

thf(pushprop_lem1_gthm,definition,
    ( pushprop_lem1_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => pushprop_lem1 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(pushprop_lem1_lthm,definition,
    ( pushprop_lem1_lthm
    = ( axvarcons
     => ( axclos
       => ( axshiftcons
         => ( ulamvarind
           => pushprop_lem1 ) ) ) ) )).

thf(pushprop_lem1v2,definition,
    ( pushprop_lem1v2
    = ( ! [P: term > $o,Q: term > $o,A: term,M: subst] :
          ( ( P @ A )
         => ( ( pushprop_p_and_p_prime @ A @ M @ P @ Q )
           => ( Q @ one ) ) ) ) )).

thf(pushprop_lem1v2_gthm,definition,
    ( pushprop_lem1v2_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => pushprop_lem1v2 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(pushprop_lem1v2_lthm,definition,
    ( pushprop_lem1v2_lthm
    = ( axvarcons
     => pushprop_lem1v2 ) )).

thf(pushprop_lem2v2,definition,
    ( pushprop_lem2v2
    = ( ! [P: term > $o,Q: term > $o,A: term,M: subst] :
          ( ( pushprop_p_and_p_prime @ A @ M @ P @ Q )
         => ( ! [B: term] :
                ( ( var @ B )
               => ( P @ ( sub @ B @ M ) ) )
           => ! [C: term] :
                ( ( var @ C )
               => ( ( Q @ C )
                 => ( Q @ ( sub @ C @ sh ) ) ) ) ) ) ) )).

thf(pushprop_lem2v2_gthm,definition,
    ( pushprop_lem2v2_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => pushprop_lem2v2 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(pushprop_lem2v2_lthm,definition,
    ( pushprop_lem2v2_lthm
    = ( axclos
     => ( axshiftcons
       => pushprop_lem2v2 ) ) )).

thf(pushprop_lem3v2,definition,
    ( pushprop_lem3v2
    = ( ! [P: term > $o,Q: term > $o,A: term,M: subst] :
          ( ( pushprop_p_and_p_prime @ A @ M @ P @ Q )
         => ( ! [B: term] :
                ( ( var @ B )
               => ( Q @ B ) )
           => ! [B: term] :
                ( ( var @ B )
               => ( P @ ( sub @ B @ ( push @ A @ M ) ) ) ) ) ) ) )).

thf(pushprop_lem3v2_lthm,definition,(
    pushprop_lem3v2_lthm = pushprop_lem3v2 )).

thf(pushprop,definition,
    ( pushprop
    = ( ! [P: term > $o,A: term,M: subst] :
          ( ! [B: term] :
              ( ( var @ B )
             => ( P @ ( sub @ B @ M ) ) )
         => ( ( P @ A )
           => ! [B: term] :
                ( ( var @ B )
               => ( P @ ( sub @ B @ ( push @ A @ M ) ) ) ) ) ) ) )).

thf(pushprop_gthm,definition,
    ( pushprop_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => pushprop ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(pushprop_lthm_orig,definition,
    ( pushprop_lthm_orig
    = ( ulamvar1
     => ( axvarcons
       => ( axclos
         => ( axshiftcons
           => ( ulamvarind
             => pushprop ) ) ) ) ) )).

thf(pushprop_lthm,definition,
    ( pushprop_lthm
    = ( pushprop_lem0
     => ( ulamvar1
       => ( axvarcons
         => ( axclos
           => ( axshiftcons
             => ( ulamvarind
               => pushprop ) ) ) ) ) ) )).

thf(induction2lem,definition,
    ( induction2lem
    = ( ! [P: term > $o] :
          ( ! [A: term,B: term] :
              ( ( P @ A )
             => ( ( P @ B )
               => ( P @ ( ap @ A @ B ) ) ) )
         => ( ! [A: term] :
                ( ! [B: term] :
                    ( ( P @ B )
                   => ( P @ ( sub @ A @ ( push @ B @ id ) ) ) )
               => ( P @ ( lam @ A ) ) )
           => ! [A: term,M: subst] :
                ( ! [B: term] :
                    ( ( var @ B )
                   => ( P @ ( sub @ B @ M ) ) )
               => ( P @ ( sub @ A @ M ) ) ) ) ) ) )).

thf(induction2lem_gthm,definition,
    ( induction2lem_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => induction2lem ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(induction2lem_lthm,definition,
    ( induction2lem_lthm
    = ( axapp
     => ( axvarcons
       => ( axabs
         => ( axclos
           => ( axshiftcons
             => ( axassoc
               => ( axmap
                 => ( axidr
                   => ( induction
                     => ( pushprop
                       => induction2lem ) ) ) ) ) ) ) ) ) ) )).

thf(induction2,definition,
    ( induction2
    = ( ! [P: term > $o] :
          ( ! [A: term] :
              ( ( var @ A )
             => ( P @ A ) )
         => ( ! [A: term,B: term] :
                ( ( P @ A )
               => ( ( P @ B )
                 => ( P @ ( ap @ A @ B ) ) ) )
           => ( ! [A: term] :
                  ( ! [B: term] :
                      ( ( P @ B )
                     => ( P @ ( sub @ A @ ( push @ B @ id ) ) ) )
                 => ( P @ ( lam @ A ) ) )
             => ! [A: term] :
                  ( P @ A ) ) ) ) ) )).

thf(induction2_gthm,definition,
    ( induction2_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => induction2 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(induction2_lthm,definition,
    ( induction2_lthm
    = ( axvarid
     => ( induction2lem
       => induction2 ) ) )).

thf(substmonoid,definition,
    ( substmonoid
    = ( ! [M: subst,N: subst,K: subst] :
          ( ( comp @ ( comp @ M @ N ) @ K )
          = ( comp @ M @ ( comp @ N @ K ) ) )
      & ! [M: subst] :
          ( ( comp @ id @ M )
          = M )
      & ! [M: subst] :
          ( ( comp @ M @ id )
          = M ) ) )).

thf(substmonoid_gthm,definition,
    ( substmonoid_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => substmonoid ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(substmonoid_lthm,definition,
    ( substmonoid_lthm
    = ( axidl
     => ( axassoc
       => ( axidr
         => substmonoid ) ) ) )).

thf(termmset,definition,
    ( termmset
    = ( ! [A: term,M: subst,N: subst] :
          ( ( sub @ ( sub @ A @ M ) @ N )
          = ( sub @ A @ ( comp @ M @ N ) ) )
      & ! [A: term] :
          ( ( sub @ A @ id )
          = A ) ) )).

thf(termmset_gthm,definition,
    ( termmset_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => ( substmonoid
                                                         => termmset ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(termmset_lthm,definition,
    ( termmset_lthm
    = ( axvarid
     => ( axclos
       => termmset ) ) )).

thf(hoasap,definition,
    ( hoasap
    = ( ^ [M: subst,A: term,N: subst,B: term] :
          ( ap @ ( sub @ A @ N ) @ B ) ) )).

thf(hoaslam,definition,
    ( hoaslam
    = ( ^ [M: subst,F: subst > term > term] :
          ( lam @ ( F @ sh @ one ) ) ) )).

thf(hoasvar,definition,
    ( hoasvar
    = ( ^ [M: subst,A: term,N: subst] :
          ( var @ ( sub @ A @ N ) ) ) )).

thf(hoasapinj1,definition,
    ( hoasapinj1
    = ( ! [A: term,B: term,C: term,D: term] :
          ( ( ( hoasap @ id @ A @ id @ C )
            = ( hoasap @ id @ B @ id @ D ) )
         => ( A = B ) ) ) )).

thf(hoasapinj1_gthm,definition,
    ( hoasapinj1_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => ( substmonoid
                                                         => ( termmset
                                                           => hoasapinj1 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(hoasapinj1_lthm,definition,
    ( hoasapinj1_lthm
    = ( axvarid
     => ( apinj1
       => hoasapinj1 ) ) )).

thf(hoasapinj2,definition,
    ( hoasapinj2
    = ( ! [A: term,B: term,C: term,D: term] :
          ( ( ( hoasap @ id @ A @ id @ C )
            = ( hoasap @ id @ B @ id @ D ) )
         => ( C = D ) ) ) )).

thf(hoasapinj2_gthm,definition,
    ( hoasapinj2_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => ( substmonoid
                                                         => ( termmset
                                                           => ( hoasapinj1
                                                             => hoasapinj2 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(hoasapinj2_lthm,definition,
    ( hoasapinj2_lthm
    = ( apinj2
     => hoasapinj2 ) )).

thf(hoaslaminj,definition,
    ( hoaslaminj
    = ( ! [F: subst > term > term] :
          ( ! [M: subst,A: term,N: subst] :
              ( ( sub @ ( F @ M @ A ) @ N )
              = ( F @ ( comp @ M @ N ) @ ( sub @ A @ N ) ) )
         => ! [G: subst > term > term] :
              ( ! [M: subst,A: term,N: subst] :
                  ( ( sub @ ( G @ M @ A ) @ N )
                  = ( G @ ( comp @ M @ N ) @ ( sub @ A @ N ) ) )
             => ( ( ( hoaslam @ id
                    @ ^ [M: subst,A: term] :
                        ( F @ M @ A ) )
                  = ( hoaslam @ id
                    @ ^ [M: subst,A: term] :
                        ( G @ M @ A ) ) )
               => ! [M: subst,A: term] :
                    ( ( F @ M @ A )
                    = ( G @ M @ A ) ) ) ) ) ) )).

thf(hoaslaminj_gthm,definition,
    ( hoaslaminj_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => ( substmonoid
                                                         => ( termmset
                                                           => ( hoasapinj1
                                                             => ( hoasapinj2
                                                               => hoaslaminj ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(hoaslaminj_lthm,definition,
    ( hoaslaminj_lthm
    = ( axvarcons
     => ( axshiftcons
       => ( laminj
         => hoaslaminj ) ) ) )).

thf(hoaslamnotap,definition,
    ( hoaslamnotap
    = ( ! [F: subst > term > term] :
          ( ! [M: subst,A: term,N: subst] :
              ( ( sub @ ( F @ M @ A ) @ N )
              = ( F @ ( comp @ M @ N ) @ ( sub @ A @ N ) ) )
         => ! [A: term,B: term] :
              ( ( hoaslam @ id
                @ ^ [M: subst,C: term] :
                    ( F @ M @ C ) )
             != ( hoasap @ id @ A @ id @ B ) ) ) ) )).

thf(hoaslamnotap_gthm,definition,
    ( hoaslamnotap_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => ( substmonoid
                                                         => ( termmset
                                                           => ( hoasapinj1
                                                             => ( hoasapinj2
                                                               => ( hoaslaminj
                                                                 => hoaslamnotap ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(hoaslamnotap_lthm,definition,
    ( hoaslamnotap_lthm
    = ( lamnotap
     => hoaslamnotap ) )).

thf(hoaslamnotvar,definition,
    ( hoaslamnotvar
    = ( ! [F: subst > term > term] :
          ( ! [M: subst,A: term,N: subst] :
              ( ( sub @ ( F @ M @ A ) @ N )
              = ( F @ ( comp @ M @ N ) @ ( sub @ A @ N ) ) )
         => ~ ( hoasvar @ id
              @ ( hoaslam @ id
                @ ^ [M: subst,A: term] :
                    ( F @ M @ A ) )
              @ id ) ) ) )).

thf(hoaslamnotvar_gthm,definition,
    ( hoaslamnotvar_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => ( substmonoid
                                                         => ( termmset
                                                           => ( hoasapinj1
                                                             => ( hoasapinj2
                                                               => ( hoaslaminj
                                                                 => ( hoaslamnotap
                                                                   => hoaslamnotvar ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(hoaslamnotvar_lthm,definition,
    ( hoaslamnotvar_lthm
    = ( axvarid
     => ( lamnotvar
       => hoaslamnotvar ) ) )).

thf(hoasapnotvar,definition,
    ( hoasapnotvar
    = ( ! [A: term,B: term] :
          ~ ( hoasvar @ id @ ( hoasap @ id @ A @ id @ B ) @ id ) ) )).

thf(hoasapnotvar_gthm,definition,
    ( hoasapnotvar_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => ( substmonoid
                                                         => ( termmset
                                                           => ( hoasapinj1
                                                             => ( hoasapinj2
                                                               => ( hoaslaminj
                                                                 => ( hoaslamnotap
                                                                   => ( hoaslamnotvar
                                                                     => hoasapnotvar ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(hoasapnotvar_lthm,definition,
    ( hoasapnotvar_lthm
    = ( axvarid
     => ( apnotvar
       => hoasapnotvar ) ) )).

thf(hoasinduction_p_and_p_prime,definition,
    ( hoasinduction_p_and_p_prime
    = ( ^ [P: subst > term > subst > $o,Q: term > $o] :
        ! [X: term] :
          ( ( Q @ X )
        <=> ( P @ id @ X @ id ) ) ) )).

thf(hoasinduction_lem0,definition,
    ( hoasinduction_lem0
    = ( ! [P: subst > term > subst > $o] :
        ? [Q: term > $o] :
          ( hoasinduction_p_and_p_prime @ P @ Q ) ) )).

thf(hoasinduction_lem0_lthm,definition,(
    hoasinduction_lem0_lthm = hoasinduction_lem0 )).

thf(hoasinduction_lem1v2,definition,
    ( hoasinduction_lem1v2
    = ( ! [P: subst > term > subst > $o,Q: term > $o] :
          ( ! [M: subst,A: term,N: subst,K: subst] :
              ( ( P @ M @ A @ ( comp @ K @ N ) )
             => ( P @ ( comp @ M @ K ) @ ( sub @ A @ K ) @ N ) )
         => ( ! [M: subst,A: term,N: subst,K: subst] :
                ( ( P @ ( comp @ M @ K ) @ ( sub @ A @ K ) @ N )
               => ( P @ M @ A @ ( comp @ K @ N ) ) )
           => ( ! [A: term] :
                  ( ( hoasvar @ id @ A @ id )
                 => ( P @ id @ A @ id ) )
             => ( ( hoasinduction_p_and_p_prime @ P @ Q )
               => ! [A: term] :
                    ( ( var @ A )
                   => ( Q @ A ) ) ) ) ) ) ) )).

thf(hoasinduction_lem1v2_gthm,definition,
    ( hoasinduction_lem1v2_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => ( substmonoid
                                                         => ( termmset
                                                           => ( hoasapinj1
                                                             => ( hoasapinj2
                                                               => ( hoaslaminj
                                                                 => ( hoaslamnotap
                                                                   => ( hoaslamnotvar
                                                                     => ( hoasapnotvar
                                                                       => hoasinduction_lem1v2 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(hoasinduction_lem2v2,definition,
    ( hoasinduction_lem2v2
    = ( ! [P: subst > term > subst > $o,Q: term > $o] :
          ( ! [M: subst,A: term,N: subst,K: subst] :
              ( ( P @ M @ A @ ( comp @ K @ N ) )
             => ( P @ ( comp @ M @ K ) @ ( sub @ A @ K ) @ N ) )
         => ( ! [M: subst,A: term,N: subst,K: subst] :
                ( ( P @ ( comp @ M @ K ) @ ( sub @ A @ K ) @ N )
               => ( P @ M @ A @ ( comp @ K @ N ) ) )
           => ( ! [A: term,B: term] :
                  ( ( P @ id @ A @ id )
                 => ( ( P @ id @ B @ id )
                   => ( P @ id @ ( hoasap @ id @ A @ id @ B ) @ id ) ) )
             => ( ( hoasinduction_p_and_p_prime @ P @ Q )
               => ! [A: term,B: term] :
                    ( ( Q @ A )
                   => ( ( Q @ B )
                     => ( Q @ ( ap @ A @ B ) ) ) ) ) ) ) ) ) )).

thf(hoasinduction_lem2v2_gthm,definition,
    ( hoasinduction_lem2v2_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => ( substmonoid
                                                         => ( termmset
                                                           => ( hoasapinj1
                                                             => ( hoasapinj2
                                                               => ( hoaslaminj
                                                                 => ( hoaslamnotap
                                                                   => ( hoaslamnotvar
                                                                     => ( hoasapnotvar
                                                                       => hoasinduction_lem2v2 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(hoasinduction_lem3v2_f,definition,
    ( hoasinduction_lem3v2_f
    = ( ! [B: term] :
        ? [F: subst > term > term] :
        ! [A: term,M: subst] :
          ( ( F @ M @ A )
          = ( sub @ B @ ( push @ A @ M ) ) ) ) )).

thf(hoasinduction_lem3v2_f_lthm,definition,(
    hoasinduction_lem3v2_f_lthm = hoasinduction_lem3v2_f )).

thf(hoasinduction_lem3v2,definition,
    ( hoasinduction_lem3v2
    = ( ! [P: subst > term > subst > $o,Q: term > $o] :
          ( ! [M: subst,A: term,N: subst,K: subst] :
              ( ( P @ M @ A @ ( comp @ K @ N ) )
             => ( P @ ( comp @ M @ K ) @ ( sub @ A @ K ) @ N ) )
         => ( ! [M: subst,A: term,N: subst,K: subst] :
                ( ( P @ ( comp @ M @ K ) @ ( sub @ A @ K ) @ N )
               => ( P @ M @ A @ ( comp @ K @ N ) ) )
           => ( ! [F: subst > term > term] :
                  ( ! [M: subst,A: term,N: subst] :
                      ( ( sub @ ( F @ M @ A ) @ N )
                      = ( F @ ( comp @ M @ N ) @ ( sub @ A @ N ) ) )
                 => ( ! [A: term] :
                        ( ( P @ id @ A @ id )
                       => ( P @ id @ ( F @ id @ A ) @ id ) )
                   => ( P @ id
                      @ ( hoaslam @ id
                        @ ^ [M: subst,A: term] :
                            ( F @ M @ A ) )
                      @ id ) ) )
             => ( ( hoasinduction_p_and_p_prime @ P @ Q )
               => ! [A: term] :
                    ( ! [B: term] :
                        ( ( Q @ B )
                       => ( Q @ ( sub @ A @ ( push @ B @ id ) ) ) )
                   => ( Q @ ( lam @ A ) ) ) ) ) ) ) ) )).

thf(hoasinduction_lem3v2_gthm,definition,
    ( hoasinduction_lem3v2_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => ( substmonoid
                                                         => ( termmset
                                                           => ( hoasapinj1
                                                             => ( hoasapinj2
                                                               => ( hoaslaminj
                                                                 => ( hoaslamnotap
                                                                   => ( hoaslamnotvar
                                                                     => ( hoasapnotvar
                                                                       => hoasinduction_lem3v2 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(hoasinduction_lem3v2_lthm,definition,
    ( hoasinduction_lem3v2_lthm
    = ( axvarid
     => ( axvarshift
       => ( axclos
         => ( axmap
           => hoasinduction_lem3v2 ) ) ) ) )).

thf(hoasinduction_lem3v2a,definition,
    ( hoasinduction_lem3v2a
    = ( ! [P: subst > term > subst > $o,Q: term > $o] :
          ( ! [F: subst > term > term] :
              ( ! [M: subst,A: term,N: subst] :
                  ( ( sub @ ( F @ M @ A ) @ N )
                  = ( F @ ( comp @ M @ N ) @ ( sub @ A @ N ) ) )
             => ( ! [A: term] :
                    ( ( P @ id @ A @ id )
                   => ( P @ id @ ( F @ id @ A ) @ id ) )
               => ( P @ id
                  @ ( hoaslam @ id
                    @ ^ [M: subst,A: term] :
                        ( F @ M @ A ) )
                  @ id ) ) )
         => ( ( hoasinduction_p_and_p_prime @ P @ Q )
           => ! [A: term] :
                ( ! [B: term] :
                    ( ( Q @ B )
                   => ( Q @ ( sub @ A @ ( push @ B @ id ) ) ) )
               => ( Q @ ( lam @ A ) ) ) ) ) ) )).

thf(hoasinduction_lem3v2a_lthm,definition,
    ( hoasinduction_lem3v2a_lthm
    = ( hoasinduction_lem3v2_f
     => ( axvarid
       => ( axvarshift
         => ( axclos
           => ( axmap
             => hoasinduction_lem3v2a ) ) ) ) ) )).

thf(hoasinduction_lem1,definition,
    ( hoasinduction_lem1
    = ( ! [P: subst > term > subst > $o] :
          ( ! [M: subst,A: term,N: subst,K: subst] :
              ( ( P @ M @ A @ ( comp @ K @ N ) )
             => ( P @ ( comp @ M @ K ) @ ( sub @ A @ K ) @ N ) )
         => ( ! [M: subst,A: term,N: subst,K: subst] :
                ( ( P @ ( comp @ M @ K ) @ ( sub @ A @ K ) @ N )
               => ( P @ M @ A @ ( comp @ K @ N ) ) )
           => ( ! [A: term] :
                  ( ( hoasvar @ id @ A @ id )
                 => ( P @ id @ A @ id ) )
             => ! [A: term] :
                  ( ( var @ A )
                 => ( P @ id @ A @ id ) ) ) ) ) ) )).

thf(hoasinduction_lem1_gthm,definition,
    ( hoasinduction_lem1_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => ( substmonoid
                                                         => ( termmset
                                                           => ( hoasapinj1
                                                             => ( hoasapinj2
                                                               => ( hoaslaminj
                                                                 => ( hoaslamnotap
                                                                   => ( hoaslamnotvar
                                                                     => ( hoasapnotvar
                                                                       => hoasinduction_lem1 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(hoasinduction_lem1_lthm,definition,
    ( hoasinduction_lem1_lthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => ( substmonoid
                                                         => ( termmset
                                                           => ( hoasapinj1
                                                             => ( hoasapinj2
                                                               => ( hoaslaminj
                                                                 => ( hoaslamnotap
                                                                   => ( hoaslamnotvar
                                                                     => ( hoasapnotvar
                                                                       => hoasinduction_lem1 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(hoasinduction_lem2,definition,
    ( hoasinduction_lem2
    = ( ! [P: subst > term > subst > $o] :
          ( ! [M: subst,A: term,N: subst,K: subst] :
              ( ( P @ M @ A @ ( comp @ K @ N ) )
             => ( P @ ( comp @ M @ K ) @ ( sub @ A @ K ) @ N ) )
         => ( ! [M: subst,A: term,N: subst,K: subst] :
                ( ( P @ ( comp @ M @ K ) @ ( sub @ A @ K ) @ N )
               => ( P @ M @ A @ ( comp @ K @ N ) ) )
           => ( ! [A: term,B: term] :
                  ( ( P @ id @ A @ id )
                 => ( ( P @ id @ B @ id )
                   => ( P @ id @ ( hoasap @ id @ A @ id @ B ) @ id ) ) )
             => ! [A: term,B: term] :
                  ( ( P @ id @ A @ id )
                 => ( ( P @ id @ B @ id )
                   => ( P @ id @ ( ap @ A @ B ) @ id ) ) ) ) ) ) ) )).

thf(hoasinduction_lem2_gthm,definition,
    ( hoasinduction_lem2_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => ( substmonoid
                                                         => ( termmset
                                                           => ( hoasapinj1
                                                             => ( hoasapinj2
                                                               => ( hoaslaminj
                                                                 => ( hoaslamnotap
                                                                   => ( hoaslamnotvar
                                                                     => ( hoasapnotvar
                                                                       => hoasinduction_lem2 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(hoasinduction_lem2_lthm,definition,
    ( hoasinduction_lem2_lthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => ( substmonoid
                                                         => ( termmset
                                                           => ( hoasapinj1
                                                             => ( hoasapinj2
                                                               => ( hoaslaminj
                                                                 => ( hoaslamnotap
                                                                   => ( hoaslamnotvar
                                                                     => ( hoasapnotvar
                                                                       => hoasinduction_lem2 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(hoasinduction_lem3aa,definition,
    ( hoasinduction_lem3aa
    = ( ! [P: subst > term > subst > $o] :
          ( ! [F: subst > term > term] :
              ( ! [M: subst,A: term,N: subst] :
                  ( ( sub @ ( F @ M @ A ) @ N )
                  = ( F @ ( comp @ M @ N ) @ ( sub @ A @ N ) ) )
             => ( ! [A: term] :
                    ( ( P @ id @ A @ id )
                   => ( P @ id @ ( F @ id @ A ) @ id ) )
               => ( P @ id
                  @ ( hoaslam @ id
                    @ ^ [M: subst,A: term] :
                        ( F @ M @ A ) )
                  @ id ) ) )
         => ! [A: term] :
              ( ! [B: term] :
                  ( ( P @ id @ B @ id )
                 => ( P @ id @ ( sub @ A @ ( push @ B @ id ) ) @ id ) )
             => ( P @ id @ ( lam @ ( sub @ A @ ( push @ one @ sh ) ) ) @ id ) ) ) ) )).

thf(hoasinduction_lem3aa_lthm,definition,
    ( hoasinduction_lem3aa_lthm
    = ( axclos
     => ( axmap
       => hoasinduction_lem3aa ) ) )).

thf(hoasinduction_lem3aaa,definition,
    ( hoasinduction_lem3aaa
    = ( ! [P: subst > term > subst > $o] :
          ( ! [F: subst > term > term] :
              ( ? [C: term] :
                ! [M: subst,A: term,N: subst] :
                  ( ( ( sub @ ( F @ M @ A ) @ N )
                    = ( sub @ ( sub @ C @ ( push @ A @ M ) ) @ N ) )
                  & ( ( sub @ C @ ( push @ ( sub @ A @ N ) @ ( comp @ M @ N ) ) )
                    = ( F @ ( comp @ M @ N ) @ ( sub @ A @ N ) ) ) )
             => ( ! [A: term] :
                    ( ( P @ id @ A @ id )
                   => ( P @ id @ ( F @ id @ A ) @ id ) )
               => ( P @ id
                  @ ( hoaslam @ id
                    @ ^ [M: subst,A: term] :
                        ( F @ M @ A ) )
                  @ id ) ) )
         => ! [A: term] :
              ( ! [B: term] :
                  ( ( P @ id @ B @ id )
                 => ( P @ id @ ( sub @ A @ ( push @ B @ id ) ) @ id ) )
             => ( P @ id @ ( lam @ ( sub @ A @ ( push @ one @ sh ) ) ) @ id ) ) ) ) )).

thf(hoasinduction_lem3,definition,
    ( hoasinduction_lem3
    = ( ! [P: subst > term > subst > $o] :
          ( ! [M: subst,A: term,N: subst,K: subst] :
              ( ( P @ M @ A @ ( comp @ K @ N ) )
             => ( P @ ( comp @ M @ K ) @ ( sub @ A @ K ) @ N ) )
         => ( ! [M: subst,A: term,N: subst,K: subst] :
                ( ( P @ ( comp @ M @ K ) @ ( sub @ A @ K ) @ N )
               => ( P @ M @ A @ ( comp @ K @ N ) ) )
           => ( ! [F: subst > term > term] :
                  ( ! [M: subst,A: term,N: subst] :
                      ( ( sub @ ( F @ M @ A ) @ N )
                      = ( F @ ( comp @ M @ N ) @ ( sub @ A @ N ) ) )
                 => ( ! [A: term] :
                        ( ( P @ id @ A @ id )
                       => ( P @ id @ ( F @ id @ A ) @ id ) )
                   => ( P @ id
                      @ ( hoaslam @ id
                        @ ^ [M: subst,A: term] :
                            ( F @ M @ A ) )
                      @ id ) ) )
             => ! [A: term] :
                  ( ! [B: term] :
                      ( ( P @ id @ B @ id )
                     => ( P @ id @ ( sub @ A @ ( push @ B @ id ) ) @ id ) )
                 => ( P @ id @ ( lam @ A ) @ id ) ) ) ) ) ) )).

thf(hoasinduction_lem3_gthm,definition,
    ( hoasinduction_lem3_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => ( substmonoid
                                                         => ( termmset
                                                           => ( hoasapinj1
                                                             => ( hoasapinj2
                                                               => ( hoaslaminj
                                                                 => ( hoaslamnotap
                                                                   => ( hoaslamnotvar
                                                                     => ( hoasapnotvar
                                                                       => ( hoasinduction_lem1
                                                                         => ( hoasinduction_lem2
                                                                           => hoasinduction_lem3 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(hoasinduction_lem3_lthm,definition,
    ( hoasinduction_lem3_lthm
    = ( axvarid
     => ( axvarshift
       => ( hoasinduction_lem3aa
         => hoasinduction_lem3 ) ) ) )).

thf(hoasinduction_lem3a,definition,
    ( hoasinduction_lem3a
    = ( ! [P: subst > term > subst > $o] :
          ( ! [F: subst > term > term] :
              ( ! [M: subst,A: term,N: subst] :
                  ( ( sub @ ( F @ M @ A ) @ N )
                  = ( F @ ( comp @ M @ N ) @ ( sub @ A @ N ) ) )
             => ( ! [A: term] :
                    ( ( P @ id @ A @ id )
                   => ( P @ id @ ( F @ id @ A ) @ id ) )
               => ( P @ id
                  @ ( hoaslam @ id
                    @ ^ [M: subst,A: term] :
                        ( F @ M @ A ) )
                  @ id ) ) )
         => ! [A: term] :
              ( ! [B: term] :
                  ( ( P @ id @ B @ id )
                 => ( P @ id @ ( sub @ A @ ( push @ B @ id ) ) @ id ) )
             => ( P @ id @ ( lam @ A ) @ id ) ) ) ) )).

thf(hoasinduction_lem3a_gthm,definition,
    ( hoasinduction_lem3a_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => ( substmonoid
                                                         => ( termmset
                                                           => ( hoasapinj1
                                                             => ( hoasapinj2
                                                               => ( hoaslaminj
                                                                 => ( hoaslamnotap
                                                                   => ( hoaslamnotvar
                                                                     => ( hoasapnotvar
                                                                       => ( hoasinduction_lem1
                                                                         => ( hoasinduction_lem2
                                                                           => hoasinduction_lem3a ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(hoasinduction_lem3a_lthm,definition,
    ( hoasinduction_lem3a_lthm
    = ( axvarid
     => ( axvarshift
       => ( hoasinduction_lem3aa
         => hoasinduction_lem3a ) ) ) )).

thf(hoasinduction_lem3b,definition,
    ( hoasinduction_lem3b
    = ( ! [B: term] :
        ? [F: subst > term > term] :
          ( ( sub @ B @ ( push @ one @ sh ) )
          = ( F @ sh @ one ) ) ) )).

thf(hoasinduction_lem3b_gthm,definition,
    ( hoasinduction_lem3b_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => ( substmonoid
                                                         => ( termmset
                                                           => ( hoasapinj1
                                                             => ( hoasapinj2
                                                               => ( hoaslaminj
                                                                 => ( hoaslamnotap
                                                                   => ( hoaslamnotvar
                                                                     => ( hoasapnotvar
                                                                       => ( hoasinduction_lem1
                                                                         => ( hoasinduction_lem2
                                                                           => hoasinduction_lem3b ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(hoasinduction_lem3b_lthm,definition,(
    hoasinduction_lem3b_lthm = hoasinduction_lem3b )).

thf(hoasinduction,definition,
    ( hoasinduction
    = ( ! [P: subst > term > subst > $o] :
          ( ! [M: subst,A: term,N: subst,K: subst] :
              ( ( P @ M @ A @ ( comp @ K @ N ) )
             => ( P @ ( comp @ M @ K ) @ ( sub @ A @ K ) @ N ) )
         => ( ! [M: subst,A: term,N: subst,K: subst] :
                ( ( P @ ( comp @ M @ K ) @ ( sub @ A @ K ) @ N )
               => ( P @ M @ A @ ( comp @ K @ N ) ) )
           => ( ! [A: term] :
                  ( ( hoasvar @ id @ A @ id )
                 => ( P @ id @ A @ id ) )
             => ( ! [A: term,B: term] :
                    ( ( P @ id @ A @ id )
                   => ( ( P @ id @ B @ id )
                     => ( P @ id @ ( hoasap @ id @ A @ id @ B ) @ id ) ) )
               => ( ! [F: subst > term > term] :
                      ( ! [M: subst,A: term,N: subst] :
                          ( ( sub @ ( F @ M @ A ) @ N )
                          = ( F @ ( comp @ M @ N ) @ ( sub @ A @ N ) ) )
                     => ( ! [A: term] :
                            ( ( P @ id @ A @ id )
                           => ( P @ id @ ( F @ id @ A ) @ id ) )
                       => ( P @ id
                          @ ( hoaslam @ id
                            @ ^ [M: subst,A: term] :
                                ( F @ M @ A ) )
                          @ id ) ) )
                 => ! [A: term] :
                      ( P @ id @ A @ id ) ) ) ) ) ) ) )).

thf(hoasinduction_gthm,definition,
    ( hoasinduction_gthm
    = ( axapp
     => ( axvarcons
       => ( axvarid
         => ( axabs
           => ( axclos
             => ( axidl
               => ( axshiftcons
                 => ( axassoc
                   => ( axmap
                     => ( axidr
                       => ( axvarshift
                         => ( axscons
                           => ( ulamvar1
                             => ( ulamvarsh
                               => ( ulamvarind
                                 => ( apinj1
                                   => ( apinj2
                                     => ( laminj
                                       => ( shinj
                                         => ( lamnotap
                                           => ( apnotvar
                                             => ( lamnotvar
                                               => ( induction
                                                 => ( pushprop
                                                   => ( induction2lem
                                                     => ( induction2
                                                       => ( substmonoid
                                                         => ( termmset
                                                           => ( hoasapinj1
                                                             => ( hoasapinj2
                                                               => ( hoaslaminj
                                                                 => ( hoaslamnotap
                                                                   => ( hoaslamnotvar
                                                                     => ( hoasapnotvar
                                                                       => ( hoasinduction_lem1
                                                                         => ( hoasinduction_lem2
                                                                           => ( hoasinduction_lem3
                                                                             => hoasinduction ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(hoasinduction_lthm,definition,
    ( hoasinduction_lthm
    = ( induction2
     => ( hoasinduction_lem1
       => ( hoasinduction_lem2
         => ( hoasinduction_lem3
           => hoasinduction ) ) ) ) )).

thf(hoasinduction_lthm_3,definition,
    ( hoasinduction_lthm_3
    = ( hoasinduction_lem0
     => ( induction2
       => ( axvarid
         => ( hoasinduction_lem3v2a
           => hoasinduction ) ) ) ) )).

thf(hoasinduction_no_psi_cond,definition,
    ( hoasinduction_no_psi_cond
    = ( ! [P: subst > term > subst > $o] :
          ( ! [A: term,B: term] :
              ( ( P @ id @ A @ id )
             => ( ( P @ id @ B @ id )
               => ( P @ id @ ( hoasap @ id @ A @ id @ B ) @ id ) ) )
         => ( ! [F: subst > term > term] :
                ( ! [M: subst,A: term,N: subst] :
                    ( ( sub @ ( F @ M @ A ) @ N )
                    = ( F @ ( comp @ M @ N ) @ ( sub @ A @ N ) ) )
               => ( ! [A: term] :
                      ( ( P @ id @ A @ id )
                     => ( P @ id @ ( F @ id @ A ) @ id ) )
                 => ( P @ id
                    @ ( hoaslam @ id
                      @ ^ [M: subst,A: term] :
                          ( F @ M @ A ) )
                    @ id ) ) )
           => ! [A: term] :
                ( P @ id @ A @ id ) ) ) ) )).

thf(hoasinduction_no_psi_cond_lthm,definition,
    ( hoasinduction_no_psi_cond_lthm
    = ( hoasinduction_lem0
     => ( induction2
       => ( axvarid
         => ( hoasinduction_lem3v2a
           => hoasinduction_no_psi_cond ) ) ) ) )).


thf(thm,conjecture,(
    pushprop_lem1v2_lthm )).

%------------------------------------------------------------------------------
