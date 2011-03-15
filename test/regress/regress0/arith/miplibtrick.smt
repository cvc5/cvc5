(benchmark miplibtrick
  :status sat
  :logic QF_LRA
  :extrafuns ((tmp1 Real))
  :extrapreds ((x177))

  :formula( and
    ( implies ( and ( not x177 ) true ) ( = tmp1 0 ) )
    ( implies ( and x177 true ) ( = tmp1 (~ 350) ) )
  )
)
