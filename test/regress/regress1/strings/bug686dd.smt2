(set-logic UFDTSLIA)
(set-info :status sat)

(declare-datatype T ((TC (TCb String))))

(declare-fun root5 () String)
(declare-fun root6 () T)

(assert (and 
(str.in_re root5 ((_ re.loop 4 4) (re.range "0" "9")) )
(str.in_re (TCb root6) ((_ re.loop 4 4) (re.range "0" "9")) )
) )
(check-sat)
