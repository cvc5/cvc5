(set-logic QF_S)
(declare-fun s () String)
(assert (xor 
            (str.<= (str.replace_all "FCBEDAC" s s) (str.replace_re "EBDCFAB" re.allchar s)) 
            (str.in_re (str.replace s "EBDCFAB" "EBDCFAB") (re.union re.allchar re.allchar))
        )
)
(set-info :status sat)
(check-sat)
