; COMMAND-LINE: --ext-rew-prep=agg --sygus-inference=try -q
; EXPECT: sat
(set-logic QF_ANIA)
(declare-fun _substvar_32_ () Bool)
(declare-fun _substvar_42_ () Bool)
(declare-const arr--2174220679694154451_3144652693758281593-0
  (Array Int (Array Int Bool)))
(assert
  (or (not
        (select
          (select arr--2174220679694154451_3144652693758281593-0 0)
          433))
      _substvar_32_))
(assert _substvar_42_)
(check-sat)
