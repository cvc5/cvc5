(set-logic QF_SLIA)
(set-option :strings-exp true)
(set-option :produce-models true)
(set-info :status sat)

(define-fun byte_2_int ((s String)) Int
  (ite (= s "\x00") 0
  (ite (= s "\x01") 1
  (ite (= s "\x02") 2
  (ite (= s "\x03") 3
  (ite (= s "\x04") 4
  (ite (= s "\x05") 5
  (ite (= s "\x06") 6
  (ite (= s "\x07") 7
  (ite (= s "\x08") 8
  (ite (= s "\x09") 9
  (ite (= s "\x0A") 10
  (ite (= s "\x0B") 11
  (ite (= s "\x0C") 12
  (ite (= s "\x0D") 13
  (ite (= s "\x0E") 14
  (ite (= s "\x0F") 15
  (ite (= s "\x10") 16
  (ite (= s "\x11") 17
  (ite (= s "\x12") 18
  (ite (= s "\x13") 19
  (ite (= s "\x14") 20
  (ite (= s "\x15") 21
  (ite (= s "\x16") 22
  (ite (= s "\x17") 23
  (ite (= s "\x18") 24
  (ite (= s "\x19") 25
  (ite (= s "\x1A") 26
  (ite (= s "\x1B") 27
  (ite (= s "\x1C") 28
  (ite (= s "\x1D") 29
  (ite (= s "\x1E") 30
  (ite (= s "\x1F") 31
  (ite (= s "\x20") 32
  (ite (= s "\x21") 33
  (ite (= s "\x22") 34
  (ite (= s "\x23") 35
  (ite (= s "\x24") 36
  (ite (= s "\x25") 37
  (ite (= s "\x26") 38
  (ite (= s "\x27") 39
  (ite (= s "\x28") 40
  (ite (= s "\x29") 41
  (ite (= s "\x2A") 42
  (ite (= s "\x2B") 43
  (ite (= s "\x2C") 44
  (ite (= s "\x2D") 45
  (ite (= s "\x2E") 46
  (ite (= s "\x2F") 47
  (ite (= s "\x30") 48
  (ite (= s "\x31") 49
  (ite (= s "\x32") 50
  (ite (= s "\x33") 51
  (ite (= s "\x34") 52
  (ite (= s "\x35") 53
  (ite (= s "\x36") 54
  (ite (= s "\x37") 55
  (ite (= s "\x38") 56
  (ite (= s "\x39") 57
  (ite (= s "\x3A") 58
  (ite (= s "\x3B") 59
  (ite (= s "\x3C") 60
  (ite (= s "\x3D") 61
  (ite (= s "\x3E") 62
  (ite (= s "\x3F") 63
  (ite (= s "\x40") 64
  (ite (= s "\x41") 65
  (ite (= s "\x42") 66
  (ite (= s "\x43") 67
  (ite (= s "\x44") 68
  (ite (= s "\x45") 69
  (ite (= s "\x46") 70
  (ite (= s "\x47") 71
  (ite (= s "\x48") 72
  (ite (= s "\x49") 73
  (ite (= s "\x4A") 74
  (ite (= s "\x4B") 75
  (ite (= s "\x4C") 76
  (ite (= s "\x4D") 77
  (ite (= s "\x4E") 78
  (ite (= s "\x4F") 79
  (ite (= s "\x50") 80
  (ite (= s "\x51") 81
  (ite (= s "\x52") 82
  (ite (= s "\x53") 83
  (ite (= s "\x54") 84
  (ite (= s "\x55") 85
  (ite (= s "\x56") 86
  (ite (= s "\x57") 87
  (ite (= s "\x58") 88
  (ite (= s "\x59") 89
  (ite (= s "\x5A") 90
  (ite (= s "\x5B") 91
  (ite (= s "\x5C") 92
  (ite (= s "\x5D") 93
  (ite (= s "\x5E") 94
  (ite (= s "\x5F") 95
  (ite (= s "\x60") 96
  (ite (= s "\x61") 97
  (ite (= s "\x62") 98
  (ite (= s "\x63") 99
  (ite (= s "\x64") 100
  (ite (= s "\x65") 101
  (ite (= s "\x66") 102
  (ite (= s "\x67") 103
  (ite (= s "\x68") 104
  (ite (= s "\x69") 105
  (ite (= s "\x6A") 106
  (ite (= s "\x6B") 107
  (ite (= s "\x6C") 108
  (ite (= s "\x6D") 109
  (ite (= s "\x6E") 110
  (ite (= s "\x6F") 111
  (ite (= s "\x70") 112
  (ite (= s "\x71") 113
  (ite (= s "\x72") 114
  (ite (= s "\x73") 115
  (ite (= s "\x74") 116
  (ite (= s "\x75") 117
  (ite (= s "\x76") 118
  (ite (= s "\x77") 119
  (ite (= s "\x78") 120
  (ite (= s "\x79") 121
  (ite (= s "\x7A") 122
  (ite (= s "\x7B") 123
  (ite (= s "\x7C") 124
  (ite (= s "\x7D") 125
  (ite (= s "\x7E") 126
  (ite (= s "\x7F") 127
  (ite (= s "\x80") 128
  (ite (= s "\x81") 129
  (ite (= s "\x82") 130
  (ite (= s "\x83") 131
  (ite (= s "\x84") 132
  (ite (= s "\x85") 133
  (ite (= s "\x86") 134
  (ite (= s "\x87") 135
  (ite (= s "\x88") 136
  (ite (= s "\x89") 137
  (ite (= s "\x8A") 138
  (ite (= s "\x8B") 139
  (ite (= s "\x8C") 140
  (ite (= s "\x8D") 141
  (ite (= s "\x8E") 142
  (ite (= s "\x8F") 143
  (ite (= s "\x90") 144
  (ite (= s "\x91") 145
  (ite (= s "\x92") 146
  (ite (= s "\x93") 147
  (ite (= s "\x94") 148
  (ite (= s "\x95") 149
  (ite (= s "\x96") 150
  (ite (= s "\x97") 151
  (ite (= s "\x98") 152
  (ite (= s "\x99") 153
  (ite (= s "\x9A") 154
  (ite (= s "\x9B") 155
  (ite (= s "\x9C") 156
  (ite (= s "\x9D") 157
  (ite (= s "\x9E") 158
  (ite (= s "\x9F") 159
  (ite (= s "\xA0") 160
  (ite (= s "\xA1") 161
  (ite (= s "\xA2") 162
  (ite (= s "\xA3") 163
  (ite (= s "\xA4") 164
  (ite (= s "\xA5") 165
  (ite (= s "\xA6") 166
  (ite (= s "\xA7") 167
  (ite (= s "\xA8") 168
  (ite (= s "\xA9") 169
  (ite (= s "\xAA") 170
  (ite (= s "\xAB") 171
  (ite (= s "\xAC") 172
  (ite (= s "\xAD") 173
  (ite (= s "\xAE") 174
  (ite (= s "\xAF") 175
  (ite (= s "\xB0") 176
  (ite (= s "\xB1") 177
  (ite (= s "\xB2") 178
  (ite (= s "\xB3") 179
  (ite (= s "\xB4") 180
  (ite (= s "\xB5") 181
  (ite (= s "\xB6") 182
  (ite (= s "\xB7") 183
  (ite (= s "\xB8") 184
  (ite (= s "\xB9") 185
  (ite (= s "\xBA") 186
  (ite (= s "\xBB") 187
  (ite (= s "\xBC") 188
  (ite (= s "\xBD") 189
  (ite (= s "\xBE") 190
  (ite (= s "\xBF") 191
  (ite (= s "\xC0") 192
  (ite (= s "\xC1") 193
  (ite (= s "\xC2") 194
  (ite (= s "\xC3") 195
  (ite (= s "\xC4") 196
  (ite (= s "\xC5") 197
  (ite (= s "\xC6") 198
  (ite (= s "\xC7") 199
  (ite (= s "\xC8") 200
  (ite (= s "\xC9") 201
  (ite (= s "\xCA") 202
  (ite (= s "\xCB") 203
  (ite (= s "\xCC") 204
  (ite (= s "\xCD") 205
  (ite (= s "\xCE") 206
  (ite (= s "\xCF") 207
  (ite (= s "\xD0") 208
  (ite (= s "\xD1") 209
  (ite (= s "\xD2") 210
  (ite (= s "\xD3") 211
  (ite (= s "\xD4") 212
  (ite (= s "\xD5") 213
  (ite (= s "\xD6") 214
  (ite (= s "\xD7") 215
  (ite (= s "\xD8") 216
  (ite (= s "\xD9") 217
  (ite (= s "\xDA") 218
  (ite (= s "\xDB") 219
  (ite (= s "\xDC") 220
  (ite (= s "\xDD") 221
  (ite (= s "\xDE") 222
  (ite (= s "\xDF") 223
  (ite (= s "\xE0") 224
  (ite (= s "\xE1") 225
  (ite (= s "\xE2") 226
  (ite (= s "\xE3") 227
  (ite (= s "\xE4") 228
  (ite (= s "\xE5") 229
  (ite (= s "\xE6") 230
  (ite (= s "\xE7") 231
  (ite (= s "\xE8") 232
  (ite (= s "\xE9") 233
  (ite (= s "\xEA") 234
  (ite (= s "\xEB") 235
  (ite (= s "\xEC") 236
  (ite (= s "\xED") 237
  (ite (= s "\xEE") 238
  (ite (= s "\xEF") 239
  (ite (= s "\xF0") 240
  (ite (= s "\xF1") 241
  (ite (= s "\xF2") 242
  (ite (= s "\xF3") 243
  (ite (= s "\xF4") 244
  (ite (= s "\xF5") 245
  (ite (= s "\xF6") 246
  (ite (= s "\xF7") 247
  (ite (= s "\xF8") 248
  (ite (= s "\xF9") 249
  (ite (= s "\xFA") 250
  (ite (= s "\xFB") 251
  (ite (= s "\xFC") 252
  (ite (= s "\xFD") 253
  (ite (= s "\xFE") 254
  (ite (= s "\xFF") 255
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
)



(define-fun read_buffer16 ((s1 String) (s2 String)) Int
  (+ (* 256 (byte_2_int s1)) 
     (byte_2_int s2))
)


(define-fun read_buffer32 ((s1 String) (s2 String) (s3 String) (s4 String)) Int
  (+ (+ (+ (* 16777216 (byte_2_int s1) )
           (*    65536 (byte_2_int s2) ) )
           (*      256 (byte_2_int s3) ) )
           (byte_2_int s4) )
)


(declare-const magic String)
(declare-const p1 String)
(declare-const p2 String)
(declare-const p3 String)
(declare-const size1 String)
(declare-const size2 String)
(declare-const size3 String)
(declare-const size4 String)
(declare-const off1 String)
(declare-const off2 String)
(declare-const off3 String)
(declare-const off4 String)
(assert (= magic "ABCD"))
(assert (= 1 (str.len size1)))
(assert (= 1 (str.len size2)))
(assert (= 1 (str.len size3)))
(assert (= 1 (str.len size4)))
(assert (= 1 (str.len off1)))
(assert (= 1 (str.len off2)))
(assert (= 1 (str.len off3)))
(assert (= 1 (str.len off4)))


(declare-const p3_off Int)
(declare-const before_p3 String)
(assert (= before_p3 (str.++ p1 p2)))
(assert (not (str.contains before_p3 magic)))
(assert (= p3_off (str.len before_p3)))


(declare-const p2_size   Int)
(declare-const p2_off    Int)
(declare-const p2_min_size  Int)
(assert (= p2_size  (read_buffer32  size1  size2  size3  size4)))
(assert (= p2_off   (read_buffer32  off1   off2   off3   off4)))
(assert (<= (+ p2_size p2_off) p3_off))
(assert (>= p2_size p2_min_size))
(assert (= p2_min_size 10))

(check-sat)
