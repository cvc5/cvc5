(set-logic UFDTSLIA)
(set-info :status sat)

(declare-datatypes ((T 0)) ( ((TC (TCb String))) ) )

(declare-fun root5 () String)
(declare-fun root6 () T)

(assert (and 
(str.in.re root5 (re.loop (re.range "0" "9") 4 4) )
(str.in.re (TCb root6) (re.loop (re.range "0" "9") 4 4) )
) )
(check-sat)
