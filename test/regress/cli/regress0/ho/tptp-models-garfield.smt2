; COMMAND-LINE: --tptp-models --force-logic=HO_ALL --mbqi
; EXPECT: sat
; EXPECT: %--------------------------------------------------------
; EXPECT: tff(human_type,type,
; EXPECT:     human: $tType ).
; EXPECT:
; EXPECT: tff(cat_type,type,
; EXPECT:     cat: $tType ).
; EXPECT:
; EXPECT: tff(jon_decl,type,
; EXPECT:     jon: human ).
; EXPECT:
; EXPECT: tff(garfield_decl,type,
; EXPECT:     garfield: cat ).
; EXPECT:
; EXPECT: tff(arlene_decl,type,
; EXPECT:     arlene: cat ).
; EXPECT:
; EXPECT: tff(nermal_decl,type,
; EXPECT:     nermal: cat ).
; EXPECT:
; EXPECT: tff(loves_decl,type,
; EXPECT:     loves: cat > cat ).
; EXPECT:
; EXPECT: tff(owns_decl,type,
; EXPECT:     owns: ( human * cat ) > $o ).
; EXPECT:
; EXPECT: %----Types of the domains
; EXPECT: tff(d_human_type,type,
; EXPECT:     d_human: $tType ).
; EXPECT:
; EXPECT: tff(d_cat_type,type,
; EXPECT:     d_cat: $tType ).
; EXPECT:
; EXPECT: %----Types of the promotion functions
; EXPECT: tff(d2human_decl,type,
; EXPECT:     d2human: d_human > human ).
; EXPECT:
; EXPECT: tff(d2cat_decl,type,
; EXPECT:     d2cat: d_cat > cat ).
; EXPECT:
; EXPECT: %----Types of the domain elements
; EXPECT: tff(d_jon_decl,type,
; EXPECT:     d_jon: d_human ).
; EXPECT:
; EXPECT: tff(d_garfield_decl,type,
; EXPECT:     d_garfield: d_cat ).
; EXPECT:
; EXPECT: tff(d_arlene_decl,type,
; EXPECT:     d_arlene: d_cat ).
; EXPECT:
; EXPECT: tff(d_nermal_decl,type,
; EXPECT:     d_nermal: d_cat ).
; EXPECT:
; EXPECT: tff(garfield,interpretation,
; EXPECT:     ( ! [H: human] :
; EXPECT:       ? [DH: d_human] :
; EXPECT:         ( H = d2human(DH) )
; EXPECT:     & ! [DH: d_human] : ( DH = d_jon )
; EXPECT:     & ! [DH1: d_human,DH2: d_human] :
; EXPECT:         ( ( d2human(DH1) = d2human(DH2) )
; EXPECT:        => ( DH1 = DH2 ) )
; EXPECT:     & ! [C: cat] :
; EXPECT:       ? [DC: d_cat] :
; EXPECT:         ( C = d2cat(DC) )
; EXPECT:     & ! [DC: d_cat] :
; EXPECT:           ( DC = d_garfield | DC = d_arlene | DC = d_nermal )
; EXPECT:     & $distinct(d_garfield,d_arlene,d_nermal)
; EXPECT:     & ! [DC1: d_cat,DC2: d_cat] :
; EXPECT:         ( ( d2cat(DC1) = d2cat(DC2) )
; EXPECT:        => ( DC1 = DC2 ) )
; EXPECT:     & ( jon = d2human(d_jon) )
; EXPECT:     & ( garfield = d2cat(d_garfield) )
; EXPECT:     & ( arlene = d2cat(d_arlene) )
; EXPECT:     & ( nermal = d2cat(d_nermal) )
; EXPECT:     & ( loves(d2cat(d_garfield)) = d2cat(d_garfield) )
; EXPECT:     & ( loves(d2cat(d_arlene)) = d2cat(d_garfield) )
; EXPECT:     & ( loves(d2cat(d_nermal)) = d2cat(d_garfield) )
; EXPECT:     & ( owns(d2human(d_jon),d2cat(d_garfield))
; EXPECT:     & ~ owns(d2human(d_jon),d2cat(d_arlene))
; EXPECT:     & ~ owns(d2human(d_jon),d2cat(d_nermal)) ) ) ).
; EXPECT: %--------------------------------------------------------
(set-option :produce-models true)
(declare-sort $$unsorted 0)
(declare-sort tptp.human 0)
(declare-sort tptp.cat 0)
(declare-fun tptp.jon () tptp.human)
(declare-fun tptp.garfield () tptp.cat)
(declare-fun tptp.arlene () tptp.cat)
(declare-fun tptp.nermal () tptp.cat)
(declare-fun tptp.loves (tptp.cat) tptp.cat)
(declare-fun tptp.owns (tptp.human tptp.cat) Bool)
(assert (forall ((H tptp.human)) (= H tptp.jon)))
(assert (forall ((C tptp.cat))
  (or (= C tptp.garfield) (= C tptp.arlene) (= C tptp.nermal))))
(assert (and (not (= tptp.garfield tptp.arlene))
             (not (= tptp.arlene tptp.nermal))
             (not (= tptp.nermal tptp.garfield))))
(assert (and (tptp.owns tptp.jon tptp.garfield)
             (not (tptp.owns tptp.jon tptp.arlene))))
(assert (forall ((C tptp.cat)) (= (tptp.loves C) tptp.garfield)))
(assert (not (forall ((C tptp.cat))
  (=> (and (= (tptp.loves C) tptp.garfield) (not (= C tptp.arlene)))
      (tptp.owns tptp.jon C)))))
(set-info :filename garfield)
(check-sat-assuming (true))
(get-model)
