import Certificates.C000
import Certificates.C001
import Certificates.C002
import Certificates.C003
import Certificates.C004
import Certificates.C005
import Certificates.C006
import Certificates.C007
import Certificates.C008
import Certificates.C009
import Certificates.C010
import Certificates.C011
import Certificates.C012
import Certificates.C013
import Certificates.C014
import Certificates.C015
import Certificates.C016
import Certificates.C017
import Certificates.C018
import Certificates.C019
import Certificates.C020
import Certificates.C021
import Certificates.C022
import Certificates.C023
import Certificates.C024
import Certificates.C025
import Certificates.C026
import Certificates.C027
import Certificates.C028
import Certificates.C029
import Certificates.C030
import Certificates.C031
import Certificates.C032
import Certificates.C033
import Certificates.C034
import Certificates.C035
import Certificates.C036
import Certificates.C037
import Certificates.C038
import Certificates.C039
import Certificates.C040
import Certificates.C041
import Certificates.C042
import Certificates.C043
import Certificates.C044
import Certificates.C045
import Certificates.C046
import Certificates.C047
import Certificates.C048
import Certificates.C049
import Certificates.C050
import Certificates.C051
import Certificates.C052
import Certificates.C053
import Certificates.C054
import Certificates.C055
import Certificates.C056
import Certificates.C057
import Certificates.C058
import Certificates.C059
import Certificates.C060
import Certificates.C061
import Certificates.C062
import Certificates.C063
import Certificates.C064
import Certificates.C065
import Certificates.C066
import Certificates.C067
import Certificates.C068
import Certificates.C069
import Certificates.C070
import Certificates.C071
import Certificates.C072
import Certificates.C073
import Certificates.C074
import Certificates.C075
import Certificates.C076
import Certificates.C077
import Certificates.C078
import Certificates.C079
import Certificates.C080
import Certificates.C081
import Certificates.C082
import Certificates.C083
import Certificates.C084
import Certificates.C085
import Certificates.C086
import Certificates.C087
import Certificates.C088
import Certificates.C089
import Certificates.C090
import Certificates.C091
import Certificates.C092
import Certificates.C093
import Certificates.C094
import Certificates.C095
import Certificates.C096
import Certificates.C097
import Certificates.C098
import Certificates.C099
import Certificates.C100
import Certificates.C101
import Certificates.C102
import Certificates.C103
import Certificates.C104
import Certificates.C105
import Certificates.C106
import Certificates.C107
import Certificates.C108
import Certificates.C109
import Certificates.C110
import Certificates.C111
import Certificates.C112
import Certificates.C113
import Certificates.C114
import Certificates.C115
import Certificates.C116
import Certificates.C117
import Certificates.C118
import Certificates.C119
import Certificates.C120
import Certificates.C121
import Certificates.C122
import Certificates.C123
import Certificates.C124
import Certificates.C125
import Certificates.C126
import Certificates.C127
import Certificates.C128
import Certificates.C129
import Certificates.C130
import Certificates.C131
import Certificates.C132
import Certificates.C133
import Certificates.C134
import Certificates.C135
import Certificates.C136
import Certificates.C137
import Certificates.C138
import Certificates.C139
import Certificates.C140
import Certificates.C141
import Certificates.C142
import Certificates.C143
import Certificates.C144
import Certificates.C145
import Certificates.C146
import Certificates.C147
import Certificates.C148
import Certificates.C149
import Certificates.C150
import Certificates.C151
import Certificates.C152
import Certificates.C153
import Certificates.C154
import Certificates.C155
import Certificates.C156
import Certificates.C157
import Certificates.C158
import Certificates.C159
import Certificates.C160
import Certificates.C161
import Certificates.C162
import Certificates.C163
import Certificates.C164
import Certificates.C165
import Certificates.C166
import Certificates.C167
import Certificates.C168
import Certificates.C169
import Certificates.C170
import Certificates.C171
import Certificates.C172
import Certificates.C173
import Certificates.C174
import Certificates.C175
import Certificates.C176
import Certificates.C177
import Certificates.C178
import Certificates.C179
import Certificates.C180
import Certificates.C181
import Certificates.C182
import Certificates.C183
import Certificates.C184
import Certificates.C185
import Certificates.C186
import Certificates.C187
import Certificates.C188
import Certificates.C189
import Certificates.C190
import Certificates.C191
import Certificates.C192
import Certificates.C193
import Certificates.C194
import Certificates.C195
import Certificates.C196
import Certificates.C197
import Certificates.C198
import Certificates.C199
import Certificates.C200
import Certificates.C201
import Certificates.C202
import Certificates.C203
import Certificates.C204
import Certificates.C205
import Certificates.C206
import Certificates.C207
import Certificates.C208
import Certificates.C209
import Certificates.C210
import Certificates.C211
import Certificates.C212
import Certificates.C213
import Certificates.C214
import Certificates.C215
import Certificates.C216
import Certificates.C217
import Certificates.C218
import Certificates.C219
import Certificates.C220
import Certificates.C221
import Certificates.C222
import Certificates.C223
import Certificates.C224
import Certificates.C225
import Certificates.C226
import Certificates.C227
import Certificates.C228
import Certificates.C229
import Certificates.C230
import Certificates.C231
import Certificates.C232
import Certificates.C233
import Certificates.C234
import Certificates.C235
import Certificates.C236
import Certificates.C237
import Certificates.C238
import Certificates.C239
import Certificates.C240
import Certificates.C241
import Certificates.C242
import Certificates.C243
import Certificates.C244
import Certificates.C245
import Certificates.C246
import Certificates.C247
import Certificates.C248
import Certificates.C249
import Certificates.C250
import Certificates.C251
import Certificates.C252
import Certificates.C253
import Certificates.C254
import Certificates.C255
import Membership.M00
import Membership.M01
import Membership.M02
import Membership.M03
import Membership.M04
import Membership.M05
import Membership.M06
import Membership.M07
import Membership.M08
import Membership.M09
import Membership.M10
import Membership.M11
import Membership.M12
import Membership.M13
import Membership.M14
import Membership.M15
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12
theorem effective_nonbent_all : ∀ b : BitVec 8, ¬ IsBent effective b ↔ b ∈ effectiveNonbent := by
  rw [BitVec.forall_cons_iff]
  intro a0
  rw [BitVec.forall_cons_iff]
  intro a1
  rw [BitVec.forall_cons_iff]
  intro a2
  rw [BitVec.forall_cons_iff]
  intro a3
  rw [BitVec.forall_cons_iff]
  intro a4
  rw [BitVec.forall_cons_iff]
  intro a5
  rw [BitVec.forall_cons_iff]
  intro a6
  rw [BitVec.forall_cons_iff]
  intro a7
  rw [BitVec.forall_zero_iff]
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;> cases a6 <;> cases a7
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 0)) ↔ (BitVec.ofNat 8 0) ∈ effectiveNonbent
    constructor
    · intro _; decide
    · intro _; exact C000.not_bent
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 1)) ↔ (BitVec.ofNat 8 1) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C001.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 1) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 2)) ↔ (BitVec.ofNat 8 2) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C002.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 2) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 3)) ↔ (BitVec.ofNat 8 3) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C003.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 3) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 4)) ↔ (BitVec.ofNat 8 4) ∈ effectiveNonbent
    constructor
    · intro _; decide
    · intro _; exact C004.not_bent
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 5)) ↔ (BitVec.ofNat 8 5) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C005.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 5) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 6)) ↔ (BitVec.ofNat 8 6) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C006.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 6) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 7)) ↔ (BitVec.ofNat 8 7) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C007.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 7) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 8)) ↔ (BitVec.ofNat 8 8) ∈ effectiveNonbent
    constructor
    · intro _; decide
    · intro _; exact C008.not_bent
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 9)) ↔ (BitVec.ofNat 8 9) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C009.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 9) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 10)) ↔ (BitVec.ofNat 8 10) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C010.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 10) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 11)) ↔ (BitVec.ofNat 8 11) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C011.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 11) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 12)) ↔ (BitVec.ofNat 8 12) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C012.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 12) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 13)) ↔ (BitVec.ofNat 8 13) ∈ effectiveNonbent
    constructor
    · intro _; decide
    · intro _; exact C013.not_bent
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 14)) ↔ (BitVec.ofNat 8 14) ∈ effectiveNonbent
    constructor
    · intro _; decide
    · intro _; exact C014.not_bent
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 15)) ↔ (BitVec.ofNat 8 15) ∈ effectiveNonbent
    constructor
    · intro _; decide
    · intro _; exact C015.not_bent
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 16)) ↔ (BitVec.ofNat 8 16) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C016.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 16) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 17)) ↔ (BitVec.ofNat 8 17) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C017.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 17) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 18)) ↔ (BitVec.ofNat 8 18) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C018.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 18) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 19)) ↔ (BitVec.ofNat 8 19) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C019.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 19) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 20)) ↔ (BitVec.ofNat 8 20) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C020.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 20) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 21)) ↔ (BitVec.ofNat 8 21) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C021.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 21) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 22)) ↔ (BitVec.ofNat 8 22) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C022.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 22) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 23)) ↔ (BitVec.ofNat 8 23) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C023.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 23) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 24)) ↔ (BitVec.ofNat 8 24) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C024.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 24) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 25)) ↔ (BitVec.ofNat 8 25) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C025.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 25) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 26)) ↔ (BitVec.ofNat 8 26) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C026.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 26) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 27)) ↔ (BitVec.ofNat 8 27) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C027.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 27) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 28)) ↔ (BitVec.ofNat 8 28) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C028.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 28) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 29)) ↔ (BitVec.ofNat 8 29) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C029.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 29) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 30)) ↔ (BitVec.ofNat 8 30) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C030.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 30) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 31)) ↔ (BitVec.ofNat 8 31) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C031.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 31) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 32)) ↔ (BitVec.ofNat 8 32) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C032.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 32) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 33)) ↔ (BitVec.ofNat 8 33) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C033.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 33) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 34)) ↔ (BitVec.ofNat 8 34) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C034.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 34) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 35)) ↔ (BitVec.ofNat 8 35) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C035.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 35) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 36)) ↔ (BitVec.ofNat 8 36) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C036.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 36) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 37)) ↔ (BitVec.ofNat 8 37) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C037.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 37) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 38)) ↔ (BitVec.ofNat 8 38) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C038.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 38) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 39)) ↔ (BitVec.ofNat 8 39) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C039.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 39) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 40)) ↔ (BitVec.ofNat 8 40) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C040.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 40) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 41)) ↔ (BitVec.ofNat 8 41) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C041.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 41) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 42)) ↔ (BitVec.ofNat 8 42) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C042.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 42) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 43)) ↔ (BitVec.ofNat 8 43) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C043.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 43) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 44)) ↔ (BitVec.ofNat 8 44) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C044.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 44) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 45)) ↔ (BitVec.ofNat 8 45) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C045.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 45) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 46)) ↔ (BitVec.ofNat 8 46) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C046.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 46) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 47)) ↔ (BitVec.ofNat 8 47) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C047.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 47) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 48)) ↔ (BitVec.ofNat 8 48) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C048.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 48) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 49)) ↔ (BitVec.ofNat 8 49) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C049.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 49) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 50)) ↔ (BitVec.ofNat 8 50) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C050.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 50) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 51)) ↔ (BitVec.ofNat 8 51) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C051.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 51) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 52)) ↔ (BitVec.ofNat 8 52) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C052.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 52) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 53)) ↔ (BitVec.ofNat 8 53) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C053.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 53) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 54)) ↔ (BitVec.ofNat 8 54) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C054.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 54) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 55)) ↔ (BitVec.ofNat 8 55) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C055.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 55) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 56)) ↔ (BitVec.ofNat 8 56) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C056.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 56) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 57)) ↔ (BitVec.ofNat 8 57) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C057.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 57) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 58)) ↔ (BitVec.ofNat 8 58) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C058.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 58) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 59)) ↔ (BitVec.ofNat 8 59) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C059.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 59) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 60)) ↔ (BitVec.ofNat 8 60) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C060.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 60) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 61)) ↔ (BitVec.ofNat 8 61) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C061.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 61) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 62)) ↔ (BitVec.ofNat 8 62) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C062.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 62) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 63)) ↔ (BitVec.ofNat 8 63) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C063.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 63) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 64)) ↔ (BitVec.ofNat 8 64) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C064.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 64) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 65)) ↔ (BitVec.ofNat 8 65) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C065.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 65) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 66)) ↔ (BitVec.ofNat 8 66) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C066.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 66) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 67)) ↔ (BitVec.ofNat 8 67) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C067.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 67) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 68)) ↔ (BitVec.ofNat 8 68) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C068.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 68) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 69)) ↔ (BitVec.ofNat 8 69) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C069.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 69) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 70)) ↔ (BitVec.ofNat 8 70) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C070.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 70) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 71)) ↔ (BitVec.ofNat 8 71) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C071.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 71) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 72)) ↔ (BitVec.ofNat 8 72) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C072.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 72) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 73)) ↔ (BitVec.ofNat 8 73) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C073.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 73) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 74)) ↔ (BitVec.ofNat 8 74) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C074.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 74) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 75)) ↔ (BitVec.ofNat 8 75) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C075.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 75) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 76)) ↔ (BitVec.ofNat 8 76) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C076.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 76) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 77)) ↔ (BitVec.ofNat 8 77) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C077.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 77) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 78)) ↔ (BitVec.ofNat 8 78) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C078.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 78) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 79)) ↔ (BitVec.ofNat 8 79) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C079.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 79) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 80)) ↔ (BitVec.ofNat 8 80) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C080.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 80) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 81)) ↔ (BitVec.ofNat 8 81) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C081.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 81) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 82)) ↔ (BitVec.ofNat 8 82) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C082.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 82) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 83)) ↔ (BitVec.ofNat 8 83) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C083.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 83) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 84)) ↔ (BitVec.ofNat 8 84) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C084.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 84) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 85)) ↔ (BitVec.ofNat 8 85) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C085.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 85) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 86)) ↔ (BitVec.ofNat 8 86) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C086.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 86) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 87)) ↔ (BitVec.ofNat 8 87) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C087.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 87) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 88)) ↔ (BitVec.ofNat 8 88) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C088.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 88) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 89)) ↔ (BitVec.ofNat 8 89) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C089.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 89) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 90)) ↔ (BitVec.ofNat 8 90) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C090.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 90) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 91)) ↔ (BitVec.ofNat 8 91) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C091.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 91) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 92)) ↔ (BitVec.ofNat 8 92) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C092.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 92) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 93)) ↔ (BitVec.ofNat 8 93) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C093.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 93) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 94)) ↔ (BitVec.ofNat 8 94) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C094.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 94) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 95)) ↔ (BitVec.ofNat 8 95) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C095.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 95) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 96)) ↔ (BitVec.ofNat 8 96) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C096.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 96) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 97)) ↔ (BitVec.ofNat 8 97) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C097.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 97) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 98)) ↔ (BitVec.ofNat 8 98) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C098.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 98) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 99)) ↔ (BitVec.ofNat 8 99) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C099.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 99) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 100)) ↔ (BitVec.ofNat 8 100) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C100.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 100) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 101)) ↔ (BitVec.ofNat 8 101) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C101.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 101) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 102)) ↔ (BitVec.ofNat 8 102) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C102.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 102) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 103)) ↔ (BitVec.ofNat 8 103) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C103.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 103) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 104)) ↔ (BitVec.ofNat 8 104) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C104.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 104) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 105)) ↔ (BitVec.ofNat 8 105) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C105.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 105) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 106)) ↔ (BitVec.ofNat 8 106) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C106.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 106) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 107)) ↔ (BitVec.ofNat 8 107) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C107.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 107) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 108)) ↔ (BitVec.ofNat 8 108) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C108.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 108) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 109)) ↔ (BitVec.ofNat 8 109) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C109.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 109) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 110)) ↔ (BitVec.ofNat 8 110) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C110.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 110) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 111)) ↔ (BitVec.ofNat 8 111) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C111.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 111) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 112)) ↔ (BitVec.ofNat 8 112) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C112.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 112) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 113)) ↔ (BitVec.ofNat 8 113) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C113.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 113) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 114)) ↔ (BitVec.ofNat 8 114) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C114.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 114) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 115)) ↔ (BitVec.ofNat 8 115) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C115.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 115) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 116)) ↔ (BitVec.ofNat 8 116) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C116.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 116) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 117)) ↔ (BitVec.ofNat 8 117) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C117.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 117) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 118)) ↔ (BitVec.ofNat 8 118) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C118.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 118) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 119)) ↔ (BitVec.ofNat 8 119) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C119.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 119) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 120)) ↔ (BitVec.ofNat 8 120) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C120.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 120) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 121)) ↔ (BitVec.ofNat 8 121) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C121.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 121) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 122)) ↔ (BitVec.ofNat 8 122) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C122.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 122) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 123)) ↔ (BitVec.ofNat 8 123) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C123.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 123) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 124)) ↔ (BitVec.ofNat 8 124) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C124.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 124) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 125)) ↔ (BitVec.ofNat 8 125) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C125.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 125) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 126)) ↔ (BitVec.ofNat 8 126) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C126.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 126) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 127)) ↔ (BitVec.ofNat 8 127) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C127.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 127) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 128)) ↔ (BitVec.ofNat 8 128) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C128.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 128) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 129)) ↔ (BitVec.ofNat 8 129) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C129.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 129) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 130)) ↔ (BitVec.ofNat 8 130) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C130.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 130) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 131)) ↔ (BitVec.ofNat 8 131) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C131.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 131) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 132)) ↔ (BitVec.ofNat 8 132) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C132.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 132) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 133)) ↔ (BitVec.ofNat 8 133) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C133.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 133) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 134)) ↔ (BitVec.ofNat 8 134) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C134.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 134) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 135)) ↔ (BitVec.ofNat 8 135) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C135.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 135) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 136)) ↔ (BitVec.ofNat 8 136) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C136.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 136) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 137)) ↔ (BitVec.ofNat 8 137) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C137.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 137) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 138)) ↔ (BitVec.ofNat 8 138) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C138.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 138) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 139)) ↔ (BitVec.ofNat 8 139) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C139.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 139) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 140)) ↔ (BitVec.ofNat 8 140) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C140.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 140) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 141)) ↔ (BitVec.ofNat 8 141) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C141.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 141) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 142)) ↔ (BitVec.ofNat 8 142) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C142.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 142) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 143)) ↔ (BitVec.ofNat 8 143) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C143.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 143) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 144)) ↔ (BitVec.ofNat 8 144) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C144.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 144) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 145)) ↔ (BitVec.ofNat 8 145) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C145.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 145) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 146)) ↔ (BitVec.ofNat 8 146) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C146.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 146) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 147)) ↔ (BitVec.ofNat 8 147) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C147.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 147) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 148)) ↔ (BitVec.ofNat 8 148) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C148.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 148) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 149)) ↔ (BitVec.ofNat 8 149) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C149.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 149) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 150)) ↔ (BitVec.ofNat 8 150) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C150.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 150) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 151)) ↔ (BitVec.ofNat 8 151) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C151.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 151) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 152)) ↔ (BitVec.ofNat 8 152) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C152.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 152) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 153)) ↔ (BitVec.ofNat 8 153) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C153.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 153) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 154)) ↔ (BitVec.ofNat 8 154) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C154.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 154) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 155)) ↔ (BitVec.ofNat 8 155) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C155.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 155) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 156)) ↔ (BitVec.ofNat 8 156) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C156.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 156) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 157)) ↔ (BitVec.ofNat 8 157) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C157.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 157) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 158)) ↔ (BitVec.ofNat 8 158) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C158.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 158) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 159)) ↔ (BitVec.ofNat 8 159) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C159.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 159) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 160)) ↔ (BitVec.ofNat 8 160) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C160.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 160) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 161)) ↔ (BitVec.ofNat 8 161) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C161.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 161) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 162)) ↔ (BitVec.ofNat 8 162) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C162.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 162) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 163)) ↔ (BitVec.ofNat 8 163) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C163.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 163) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 164)) ↔ (BitVec.ofNat 8 164) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C164.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 164) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 165)) ↔ (BitVec.ofNat 8 165) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C165.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 165) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 166)) ↔ (BitVec.ofNat 8 166) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C166.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 166) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 167)) ↔ (BitVec.ofNat 8 167) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C167.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 167) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 168)) ↔ (BitVec.ofNat 8 168) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C168.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 168) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 169)) ↔ (BitVec.ofNat 8 169) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C169.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 169) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 170)) ↔ (BitVec.ofNat 8 170) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C170.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 170) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 171)) ↔ (BitVec.ofNat 8 171) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C171.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 171) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 172)) ↔ (BitVec.ofNat 8 172) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C172.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 172) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 173)) ↔ (BitVec.ofNat 8 173) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C173.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 173) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 174)) ↔ (BitVec.ofNat 8 174) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C174.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 174) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 175)) ↔ (BitVec.ofNat 8 175) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C175.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 175) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 176)) ↔ (BitVec.ofNat 8 176) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C176.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 176) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 177)) ↔ (BitVec.ofNat 8 177) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C177.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 177) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 178)) ↔ (BitVec.ofNat 8 178) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C178.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 178) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 179)) ↔ (BitVec.ofNat 8 179) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C179.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 179) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 180)) ↔ (BitVec.ofNat 8 180) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C180.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 180) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 181)) ↔ (BitVec.ofNat 8 181) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C181.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 181) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 182)) ↔ (BitVec.ofNat 8 182) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C182.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 182) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 183)) ↔ (BitVec.ofNat 8 183) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C183.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 183) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 184)) ↔ (BitVec.ofNat 8 184) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C184.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 184) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 185)) ↔ (BitVec.ofNat 8 185) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C185.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 185) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 186)) ↔ (BitVec.ofNat 8 186) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C186.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 186) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 187)) ↔ (BitVec.ofNat 8 187) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C187.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 187) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 188)) ↔ (BitVec.ofNat 8 188) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C188.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 188) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 189)) ↔ (BitVec.ofNat 8 189) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C189.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 189) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 190)) ↔ (BitVec.ofNat 8 190) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C190.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 190) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 191)) ↔ (BitVec.ofNat 8 191) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C191.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 191) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 192)) ↔ (BitVec.ofNat 8 192) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C192.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 192) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 193)) ↔ (BitVec.ofNat 8 193) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C193.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 193) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 194)) ↔ (BitVec.ofNat 8 194) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C194.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 194) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 195)) ↔ (BitVec.ofNat 8 195) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C195.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 195) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 196)) ↔ (BitVec.ofNat 8 196) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C196.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 196) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 197)) ↔ (BitVec.ofNat 8 197) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C197.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 197) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 198)) ↔ (BitVec.ofNat 8 198) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C198.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 198) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 199)) ↔ (BitVec.ofNat 8 199) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C199.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 199) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 200)) ↔ (BitVec.ofNat 8 200) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C200.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 200) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 201)) ↔ (BitVec.ofNat 8 201) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C201.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 201) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 202)) ↔ (BitVec.ofNat 8 202) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C202.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 202) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 203)) ↔ (BitVec.ofNat 8 203) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C203.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 203) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 204)) ↔ (BitVec.ofNat 8 204) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C204.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 204) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 205)) ↔ (BitVec.ofNat 8 205) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C205.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 205) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 206)) ↔ (BitVec.ofNat 8 206) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C206.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 206) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 207)) ↔ (BitVec.ofNat 8 207) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C207.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 207) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 208)) ↔ (BitVec.ofNat 8 208) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C208.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 208) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 209)) ↔ (BitVec.ofNat 8 209) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C209.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 209) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 210)) ↔ (BitVec.ofNat 8 210) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C210.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 210) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 211)) ↔ (BitVec.ofNat 8 211) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C211.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 211) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 212)) ↔ (BitVec.ofNat 8 212) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C212.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 212) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 213)) ↔ (BitVec.ofNat 8 213) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C213.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 213) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 214)) ↔ (BitVec.ofNat 8 214) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C214.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 214) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 215)) ↔ (BitVec.ofNat 8 215) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C215.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 215) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 216)) ↔ (BitVec.ofNat 8 216) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C216.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 216) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 217)) ↔ (BitVec.ofNat 8 217) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C217.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 217) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 218)) ↔ (BitVec.ofNat 8 218) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C218.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 218) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 219)) ↔ (BitVec.ofNat 8 219) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C219.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 219) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 220)) ↔ (BitVec.ofNat 8 220) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C220.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 220) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 221)) ↔ (BitVec.ofNat 8 221) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C221.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 221) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 222)) ↔ (BitVec.ofNat 8 222) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C222.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 222) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 223)) ↔ (BitVec.ofNat 8 223) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C223.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 223) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 224)) ↔ (BitVec.ofNat 8 224) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C224.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 224) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 225)) ↔ (BitVec.ofNat 8 225) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C225.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 225) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 226)) ↔ (BitVec.ofNat 8 226) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C226.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 226) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 227)) ↔ (BitVec.ofNat 8 227) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C227.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 227) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 228)) ↔ (BitVec.ofNat 8 228) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C228.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 228) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 229)) ↔ (BitVec.ofNat 8 229) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C229.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 229) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 230)) ↔ (BitVec.ofNat 8 230) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C230.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 230) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 231)) ↔ (BitVec.ofNat 8 231) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C231.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 231) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 232)) ↔ (BitVec.ofNat 8 232) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C232.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 232) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 233)) ↔ (BitVec.ofNat 8 233) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C233.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 233) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 234)) ↔ (BitVec.ofNat 8 234) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C234.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 234) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 235)) ↔ (BitVec.ofNat 8 235) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C235.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 235) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 236)) ↔ (BitVec.ofNat 8 236) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C236.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 236) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 237)) ↔ (BitVec.ofNat 8 237) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C237.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 237) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 238)) ↔ (BitVec.ofNat 8 238) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C238.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 238) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 239)) ↔ (BitVec.ofNat 8 239) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C239.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 239) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 240)) ↔ (BitVec.ofNat 8 240) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C240.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 240) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 241)) ↔ (BitVec.ofNat 8 241) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C241.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 241) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 242)) ↔ (BitVec.ofNat 8 242) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C242.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 242) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 243)) ↔ (BitVec.ofNat 8 243) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C243.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 243) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 244)) ↔ (BitVec.ofNat 8 244) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C244.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 244) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 245)) ↔ (BitVec.ofNat 8 245) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C245.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 245) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 246)) ↔ (BitVec.ofNat 8 246) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C246.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 246) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 247)) ↔ (BitVec.ofNat 8 247) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C247.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 247) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 248)) ↔ (BitVec.ofNat 8 248) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C248.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 248) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 249)) ↔ (BitVec.ofNat 8 249) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C249.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 249) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 250)) ↔ (BitVec.ofNat 8 250) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C250.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 250) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 251)) ↔ (BitVec.ofNat 8 251) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C251.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 251) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 252)) ↔ (BitVec.ofNat 8 252) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C252.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 252) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 253)) ↔ (BitVec.ofNat 8 253) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C253.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 253) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 254)) ↔ (BitVec.ofNat 8 254) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C254.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 254) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)
  ·
    change (¬ IsBent effective (BitVec.ofNat 8 255)) ↔ (BitVec.ofNat 8 255) ∈ effectiveNonbent
    constructor
    · intro h; exact False.elim (h C255.bent)
    · intro h
      have hn : ¬ (BitVec.ofNat 8 255) ∈ effectiveNonbent := by decide
      exact False.elim (hn h)

theorem effective_nonbent_iff (b : BitVec 8) : ¬ IsBent effective b ↔ b ∈ effectiveNonbent := effective_nonbent_all b

theorem membership_iff : ∀ b : BitVec 12,
    ((b ≠ 0 ∧ b.setWidth 8 ∈ effectiveNonbent) ↔ b ∈ nonbentMasks) := by
  rw [BitVec.forall_cons_iff]
  intro a
  rw [BitVec.forall_cons_iff]
  intro b
  rw [BitVec.forall_cons_iff]
  intro c
  rw [BitVec.forall_cons_iff]
  intro d
  cases a <;> cases b <;> cases c <;> cases d
  · exact membership00
  · exact membership01
  · exact membership02
  · exact membership03
  · exact membership04
  · exact membership05
  · exact membership06
  · exact membership07
  · exact membership08
  · exact membership09
  · exact membership10
  · exact membership11
  · exact membership12
  · exact membership13
  · exact membership14
  · exact membership15
theorem exact_nonbent_masks (b : BitVec 12) :
    (b ≠ 0 ∧ ¬ IsBent F b) ↔ b ∈ nonbentMasks := by
  rw [F_bent_iff, effective_nonbent_iff]
  exact membership_iff b

/-- Exact-degree-two, twelve-input/twelve-output witness with95 nonzero nonbent components. -/
theorem exists_exactly_quadratic_with_ninety_five_nonbent_components :
  ∃ (f : BitVec 12 → BitVec 12) (S : List (BitVec 12)),
    IsHomogeneousQuadratic f ∧ ¬ IsAffine f ∧ S.Nodup ∧ S.length = 95 ∧
    ∀ b, (b ≠ 0 ∧ ¬ IsBent f b) ↔ b ∈ S := by
  exact ⟨F, nonbentMasks, F_quadratic, F_nonaffine, nonbentMasks_nodup,
    nonbentMasks_length, exact_nonbent_masks⟩

#print axioms exists_exactly_quadratic_with_ninety_five_nonbent_components
#print axioms exact_nonbent_masks
#print axioms F_quadratic
#print axioms F_nonaffine
end N12
