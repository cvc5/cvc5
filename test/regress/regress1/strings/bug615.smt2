(set-info :smt-lib-version 2.6)
(set-logic QF_S)
(set-option :strings-exp true)
(set-info :status sat)

(declare-fun s () String)
;(assert (= s "</script><script>alert(1);</script><script>"))

(declare-fun joined () String)
(assert (= joined (str.++ "<script>console.log('" s "');</script>")))
(assert (str.contains joined "<script>alert(1);</script>"))

; (<script>[^<]*</script>)+
(assert (str.in_re joined
            (re.+ (re.++
                    (str.to_re "<script>")
                    (re.*
                        (re.union
                            (re.range " " ";")
                            (re.range "=" "~")
                        )
                    )
                    (str.to_re "</script>")
            ))
  ))

(check-sat)
