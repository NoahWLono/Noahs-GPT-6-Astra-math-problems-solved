import PrimeDivisorBlocks0
import PrimeDivisorBlocks1
import PrimeDivisorBlocks2
import PrimeDivisorBlocks3
import PrimeDivisorBlocks4
import PrimeDivisorBlocks5
import PrimeDivisorBlocks6
import PrimeDivisorBlocks7
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace ProgressivePool
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
theorem all_small_nondivisors (b : Fin 128) : ∀ r : Fin 256, 2 ≤ b.val*256+r.val → 1073741789 % (b.val*256+r.val) ≠ 0 := by
  rcases b with ⟨b,hb⟩
  change ∀ r : Fin 256, 2 ≤ b*256+r.val → 1073741789 % (b*256+r.val) ≠ 0
  interval_cases b
  · exact no_divisor_block_0
  · exact no_divisor_block_1
  · exact no_divisor_block_2
  · exact no_divisor_block_3
  · exact no_divisor_block_4
  · exact no_divisor_block_5
  · exact no_divisor_block_6
  · exact no_divisor_block_7
  · exact no_divisor_block_8
  · exact no_divisor_block_9
  · exact no_divisor_block_10
  · exact no_divisor_block_11
  · exact no_divisor_block_12
  · exact no_divisor_block_13
  · exact no_divisor_block_14
  · exact no_divisor_block_15
  · exact no_divisor_block_16
  · exact no_divisor_block_17
  · exact no_divisor_block_18
  · exact no_divisor_block_19
  · exact no_divisor_block_20
  · exact no_divisor_block_21
  · exact no_divisor_block_22
  · exact no_divisor_block_23
  · exact no_divisor_block_24
  · exact no_divisor_block_25
  · exact no_divisor_block_26
  · exact no_divisor_block_27
  · exact no_divisor_block_28
  · exact no_divisor_block_29
  · exact no_divisor_block_30
  · exact no_divisor_block_31
  · exact no_divisor_block_32
  · exact no_divisor_block_33
  · exact no_divisor_block_34
  · exact no_divisor_block_35
  · exact no_divisor_block_36
  · exact no_divisor_block_37
  · exact no_divisor_block_38
  · exact no_divisor_block_39
  · exact no_divisor_block_40
  · exact no_divisor_block_41
  · exact no_divisor_block_42
  · exact no_divisor_block_43
  · exact no_divisor_block_44
  · exact no_divisor_block_45
  · exact no_divisor_block_46
  · exact no_divisor_block_47
  · exact no_divisor_block_48
  · exact no_divisor_block_49
  · exact no_divisor_block_50
  · exact no_divisor_block_51
  · exact no_divisor_block_52
  · exact no_divisor_block_53
  · exact no_divisor_block_54
  · exact no_divisor_block_55
  · exact no_divisor_block_56
  · exact no_divisor_block_57
  · exact no_divisor_block_58
  · exact no_divisor_block_59
  · exact no_divisor_block_60
  · exact no_divisor_block_61
  · exact no_divisor_block_62
  · exact no_divisor_block_63
  · exact no_divisor_block_64
  · exact no_divisor_block_65
  · exact no_divisor_block_66
  · exact no_divisor_block_67
  · exact no_divisor_block_68
  · exact no_divisor_block_69
  · exact no_divisor_block_70
  · exact no_divisor_block_71
  · exact no_divisor_block_72
  · exact no_divisor_block_73
  · exact no_divisor_block_74
  · exact no_divisor_block_75
  · exact no_divisor_block_76
  · exact no_divisor_block_77
  · exact no_divisor_block_78
  · exact no_divisor_block_79
  · exact no_divisor_block_80
  · exact no_divisor_block_81
  · exact no_divisor_block_82
  · exact no_divisor_block_83
  · exact no_divisor_block_84
  · exact no_divisor_block_85
  · exact no_divisor_block_86
  · exact no_divisor_block_87
  · exact no_divisor_block_88
  · exact no_divisor_block_89
  · exact no_divisor_block_90
  · exact no_divisor_block_91
  · exact no_divisor_block_92
  · exact no_divisor_block_93
  · exact no_divisor_block_94
  · exact no_divisor_block_95
  · exact no_divisor_block_96
  · exact no_divisor_block_97
  · exact no_divisor_block_98
  · exact no_divisor_block_99
  · exact no_divisor_block_100
  · exact no_divisor_block_101
  · exact no_divisor_block_102
  · exact no_divisor_block_103
  · exact no_divisor_block_104
  · exact no_divisor_block_105
  · exact no_divisor_block_106
  · exact no_divisor_block_107
  · exact no_divisor_block_108
  · exact no_divisor_block_109
  · exact no_divisor_block_110
  · exact no_divisor_block_111
  · exact no_divisor_block_112
  · exact no_divisor_block_113
  · exact no_divisor_block_114
  · exact no_divisor_block_115
  · exact no_divisor_block_116
  · exact no_divisor_block_117
  · exact no_divisor_block_118
  · exact no_divisor_block_119
  · exact no_divisor_block_120
  · exact no_divisor_block_121
  · exact no_divisor_block_122
  · exact no_divisor_block_123
  · exact no_divisor_block_124
  · exact no_divisor_block_125
  · exact no_divisor_block_126
  · exact no_divisor_block_127

theorem parameter_prime_checked : Nat.Prime 1073741789 := by
  apply Nat.prime_def_le_sqrt.mpr
  refine ⟨by decide, ?_⟩
  intro m hm2 hms hd
  have hsq : m*m ≤ 1073741789 := (Nat.mul_le_mul hms hms).trans (Nat.sqrt_le _)
  have hbound : m < 32768 := by nlinarith
  let b : Fin 128 := ⟨m/256, by omega⟩
  let r : Fin 256 := ⟨m%256, Nat.mod_lt _ (by decide)⟩
  have he : b.val*256+r.val = m := by
    dsimp [b,r]
    omega
  have hn := all_small_nondivisors b r (by simpa [he] using hm2)
  rw [he] at hn
  exact hn (Nat.dvd_iff_mod_eq_zero.mp hd)

#print axioms parameter_prime_checked
end ProgressivePool
