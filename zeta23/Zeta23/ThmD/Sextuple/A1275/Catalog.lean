import Zeta23.ThmD.Sextuple.A1275.RefinementData
import Zeta23.ThmD.Sextuple.Macro.ParametricAdapter
import Zeta23.ThmD.Sextuple.Macro.StableCatalog

namespace Zeta23.ThmD.Sextuple.MacroPrototype

/-- The independently checked 216-piece refinement table. -/
def refinementTable (i : Fin 216) : MacroPiece :=
  match i.val with
  | 0 => refinementPiece0
  | 1 => refinementPiece1
  | 2 => refinementPiece2
  | 3 => refinementPiece3
  | 4 => refinementPiece4
  | 5 => refinementPiece5
  | 6 => refinementPiece6
  | 7 => refinementPiece7
  | 8 => refinementPiece8
  | 9 => refinementPiece9
  | 10 => refinementPiece10
  | 11 => refinementPiece11
  | 12 => refinementPiece12
  | 13 => refinementPiece13
  | 14 => refinementPiece14
  | 15 => refinementPiece15
  | 16 => refinementPiece16
  | 17 => refinementPiece17
  | 18 => refinementPiece18
  | 19 => refinementPiece19
  | 20 => refinementPiece20
  | 21 => refinementPiece21
  | 22 => refinementPiece22
  | 23 => refinementPiece23
  | 24 => refinementPiece24
  | 25 => refinementPiece25
  | 26 => refinementPiece26
  | 27 => refinementPiece27
  | 28 => refinementPiece28
  | 29 => refinementPiece29
  | 30 => refinementPiece30
  | 31 => refinementPiece31
  | 32 => refinementPiece32
  | 33 => refinementPiece33
  | 34 => refinementPiece34
  | 35 => refinementPiece35
  | 36 => refinementPiece36
  | 37 => refinementPiece37
  | 38 => refinementPiece38
  | 39 => refinementPiece39
  | 40 => refinementPiece40
  | 41 => refinementPiece41
  | 42 => refinementPiece42
  | 43 => refinementPiece43
  | 44 => refinementPiece44
  | 45 => refinementPiece45
  | 46 => refinementPiece46
  | 47 => refinementPiece47
  | 48 => refinementPiece48
  | 49 => refinementPiece49
  | 50 => refinementPiece50
  | 51 => refinementPiece51
  | 52 => refinementPiece52
  | 53 => refinementPiece53
  | 54 => refinementPiece54
  | 55 => refinementPiece55
  | 56 => refinementPiece56
  | 57 => refinementPiece57
  | 58 => refinementPiece58
  | 59 => refinementPiece59
  | 60 => refinementPiece60
  | 61 => refinementPiece61
  | 62 => refinementPiece62
  | 63 => refinementPiece63
  | 64 => refinementPiece64
  | 65 => refinementPiece65
  | 66 => refinementPiece66
  | 67 => refinementPiece67
  | 68 => refinementPiece68
  | 69 => refinementPiece69
  | 70 => refinementPiece70
  | 71 => refinementPiece71
  | 72 => refinementPiece72
  | 73 => refinementPiece73
  | 74 => refinementPiece74
  | 75 => refinementPiece75
  | 76 => refinementPiece76
  | 77 => refinementPiece77
  | 78 => refinementPiece78
  | 79 => refinementPiece79
  | 80 => refinementPiece80
  | 81 => refinementPiece81
  | 82 => refinementPiece82
  | 83 => refinementPiece83
  | 84 => refinementPiece84
  | 85 => refinementPiece85
  | 86 => refinementPiece86
  | 87 => refinementPiece87
  | 88 => refinementPiece88
  | 89 => refinementPiece89
  | 90 => refinementPiece90
  | 91 => refinementPiece91
  | 92 => refinementPiece92
  | 93 => refinementPiece93
  | 94 => refinementPiece94
  | 95 => refinementPiece95
  | 96 => refinementPiece96
  | 97 => refinementPiece97
  | 98 => refinementPiece98
  | 99 => refinementPiece99
  | 100 => refinementPiece100
  | 101 => refinementPiece101
  | 102 => refinementPiece102
  | 103 => refinementPiece103
  | 104 => refinementPiece104
  | 105 => refinementPiece105
  | 106 => refinementPiece106
  | 107 => refinementPiece107
  | 108 => refinementPiece108
  | 109 => refinementPiece109
  | 110 => refinementPiece110
  | 111 => refinementPiece111
  | 112 => refinementPiece112
  | 113 => refinementPiece113
  | 114 => refinementPiece114
  | 115 => refinementPiece115
  | 116 => refinementPiece116
  | 117 => refinementPiece117
  | 118 => refinementPiece118
  | 119 => refinementPiece119
  | 120 => refinementPiece120
  | 121 => refinementPiece121
  | 122 => refinementPiece122
  | 123 => refinementPiece123
  | 124 => refinementPiece124
  | 125 => refinementPiece125
  | 126 => refinementPiece126
  | 127 => refinementPiece127
  | 128 => refinementPiece128
  | 129 => refinementPiece129
  | 130 => refinementPiece130
  | 131 => refinementPiece131
  | 132 => refinementPiece132
  | 133 => refinementPiece133
  | 134 => refinementPiece134
  | 135 => refinementPiece135
  | 136 => refinementPiece136
  | 137 => refinementPiece137
  | 138 => refinementPiece138
  | 139 => refinementPiece139
  | 140 => refinementPiece140
  | 141 => refinementPiece141
  | 142 => refinementPiece142
  | 143 => refinementPiece143
  | 144 => refinementPiece144
  | 145 => refinementPiece145
  | 146 => refinementPiece146
  | 147 => refinementPiece147
  | 148 => refinementPiece148
  | 149 => refinementPiece149
  | 150 => refinementPiece150
  | 151 => refinementPiece151
  | 152 => refinementPiece152
  | 153 => refinementPiece153
  | 154 => refinementPiece154
  | 155 => refinementPiece155
  | 156 => refinementPiece156
  | 157 => refinementPiece157
  | 158 => refinementPiece158
  | 159 => refinementPiece159
  | 160 => refinementPiece160
  | 161 => refinementPiece161
  | 162 => refinementPiece162
  | 163 => refinementPiece163
  | 164 => refinementPiece164
  | 165 => refinementPiece165
  | 166 => refinementPiece166
  | 167 => refinementPiece167
  | 168 => refinementPiece168
  | 169 => refinementPiece169
  | 170 => refinementPiece170
  | 171 => refinementPiece171
  | 172 => refinementPiece172
  | 173 => refinementPiece173
  | 174 => refinementPiece174
  | 175 => refinementPiece175
  | 176 => refinementPiece176
  | 177 => refinementPiece177
  | 178 => refinementPiece178
  | 179 => refinementPiece179
  | 180 => refinementPiece180
  | 181 => refinementPiece181
  | 182 => refinementPiece182
  | 183 => refinementPiece183
  | 184 => refinementPiece184
  | 185 => refinementPiece185
  | 186 => refinementPiece186
  | 187 => refinementPiece187
  | 188 => refinementPiece188
  | 189 => refinementPiece189
  | 190 => refinementPiece190
  | 191 => refinementPiece191
  | 192 => refinementPiece192
  | 193 => refinementPiece193
  | 194 => refinementPiece194
  | 195 => refinementPiece195
  | 196 => refinementPiece196
  | 197 => refinementPiece197
  | 198 => refinementPiece198
  | 199 => refinementPiece199
  | 200 => refinementPiece200
  | 201 => refinementPiece201
  | 202 => refinementPiece202
  | 203 => refinementPiece203
  | 204 => refinementPiece204
  | 205 => refinementPiece205
  | 206 => refinementPiece206
  | 207 => refinementPiece207
  | 208 => refinementPiece208
  | 209 => refinementPiece209
  | 210 => refinementPiece210
  | 211 => refinementPiece211
  | 212 => refinementPiece212
  | 213 => refinementPiece213
  | 214 => refinementPiece214
  | _ => refinementPiece215

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem refinementTable_check (i : Fin 216) : (refinementTable i).check = true := by
  fin_cases i
  · exact refinementPiece0_check
  · exact refinementPiece1_check
  · exact refinementPiece2_check
  · exact refinementPiece3_check
  · exact refinementPiece4_check
  · exact refinementPiece5_check
  · exact refinementPiece6_check
  · exact refinementPiece7_check
  · exact refinementPiece8_check
  · exact refinementPiece9_check
  · exact refinementPiece10_check
  · exact refinementPiece11_check
  · exact refinementPiece12_check
  · exact refinementPiece13_check
  · exact refinementPiece14_check
  · exact refinementPiece15_check
  · exact refinementPiece16_check
  · exact refinementPiece17_check
  · exact refinementPiece18_check
  · exact refinementPiece19_check
  · exact refinementPiece20_check
  · exact refinementPiece21_check
  · exact refinementPiece22_check
  · exact refinementPiece23_check
  · exact refinementPiece24_check
  · exact refinementPiece25_check
  · exact refinementPiece26_check
  · exact refinementPiece27_check
  · exact refinementPiece28_check
  · exact refinementPiece29_check
  · exact refinementPiece30_check
  · exact refinementPiece31_check
  · exact refinementPiece32_check
  · exact refinementPiece33_check
  · exact refinementPiece34_check
  · exact refinementPiece35_check
  · exact refinementPiece36_check
  · exact refinementPiece37_check
  · exact refinementPiece38_check
  · exact refinementPiece39_check
  · exact refinementPiece40_check
  · exact refinementPiece41_check
  · exact refinementPiece42_check
  · exact refinementPiece43_check
  · exact refinementPiece44_check
  · exact refinementPiece45_check
  · exact refinementPiece46_check
  · exact refinementPiece47_check
  · exact refinementPiece48_check
  · exact refinementPiece49_check
  · exact refinementPiece50_check
  · exact refinementPiece51_check
  · exact refinementPiece52_check
  · exact refinementPiece53_check
  · exact refinementPiece54_check
  · exact refinementPiece55_check
  · exact refinementPiece56_check
  · exact refinementPiece57_check
  · exact refinementPiece58_check
  · exact refinementPiece59_check
  · exact refinementPiece60_check
  · exact refinementPiece61_check
  · exact refinementPiece62_check
  · exact refinementPiece63_check
  · exact refinementPiece64_check
  · exact refinementPiece65_check
  · exact refinementPiece66_check
  · exact refinementPiece67_check
  · exact refinementPiece68_check
  · exact refinementPiece69_check
  · exact refinementPiece70_check
  · exact refinementPiece71_check
  · exact refinementPiece72_check
  · exact refinementPiece73_check
  · exact refinementPiece74_check
  · exact refinementPiece75_check
  · exact refinementPiece76_check
  · exact refinementPiece77_check
  · exact refinementPiece78_check
  · exact refinementPiece79_check
  · exact refinementPiece80_check
  · exact refinementPiece81_check
  · exact refinementPiece82_check
  · exact refinementPiece83_check
  · exact refinementPiece84_check
  · exact refinementPiece85_check
  · exact refinementPiece86_check
  · exact refinementPiece87_check
  · exact refinementPiece88_check
  · exact refinementPiece89_check
  · exact refinementPiece90_check
  · exact refinementPiece91_check
  · exact refinementPiece92_check
  · exact refinementPiece93_check
  · exact refinementPiece94_check
  · exact refinementPiece95_check
  · exact refinementPiece96_check
  · exact refinementPiece97_check
  · exact refinementPiece98_check
  · exact refinementPiece99_check
  · exact refinementPiece100_check
  · exact refinementPiece101_check
  · exact refinementPiece102_check
  · exact refinementPiece103_check
  · exact refinementPiece104_check
  · exact refinementPiece105_check
  · exact refinementPiece106_check
  · exact refinementPiece107_check
  · exact refinementPiece108_check
  · exact refinementPiece109_check
  · exact refinementPiece110_check
  · exact refinementPiece111_check
  · exact refinementPiece112_check
  · exact refinementPiece113_check
  · exact refinementPiece114_check
  · exact refinementPiece115_check
  · exact refinementPiece116_check
  · exact refinementPiece117_check
  · exact refinementPiece118_check
  · exact refinementPiece119_check
  · exact refinementPiece120_check
  · exact refinementPiece121_check
  · exact refinementPiece122_check
  · exact refinementPiece123_check
  · exact refinementPiece124_check
  · exact refinementPiece125_check
  · exact refinementPiece126_check
  · exact refinementPiece127_check
  · exact refinementPiece128_check
  · exact refinementPiece129_check
  · exact refinementPiece130_check
  · exact refinementPiece131_check
  · exact refinementPiece132_check
  · exact refinementPiece133_check
  · exact refinementPiece134_check
  · exact refinementPiece135_check
  · exact refinementPiece136_check
  · exact refinementPiece137_check
  · exact refinementPiece138_check
  · exact refinementPiece139_check
  · exact refinementPiece140_check
  · exact refinementPiece141_check
  · exact refinementPiece142_check
  · exact refinementPiece143_check
  · exact refinementPiece144_check
  · exact refinementPiece145_check
  · exact refinementPiece146_check
  · exact refinementPiece147_check
  · exact refinementPiece148_check
  · exact refinementPiece149_check
  · exact refinementPiece150_check
  · exact refinementPiece151_check
  · exact refinementPiece152_check
  · exact refinementPiece153_check
  · exact refinementPiece154_check
  · exact refinementPiece155_check
  · exact refinementPiece156_check
  · exact refinementPiece157_check
  · exact refinementPiece158_check
  · exact refinementPiece159_check
  · exact refinementPiece160_check
  · exact refinementPiece161_check
  · exact refinementPiece162_check
  · exact refinementPiece163_check
  · exact refinementPiece164_check
  · exact refinementPiece165_check
  · exact refinementPiece166_check
  · exact refinementPiece167_check
  · exact refinementPiece168_check
  · exact refinementPiece169_check
  · exact refinementPiece170_check
  · exact refinementPiece171_check
  · exact refinementPiece172_check
  · exact refinementPiece173_check
  · exact refinementPiece174_check
  · exact refinementPiece175_check
  · exact refinementPiece176_check
  · exact refinementPiece177_check
  · exact refinementPiece178_check
  · exact refinementPiece179_check
  · exact refinementPiece180_check
  · exact refinementPiece181_check
  · exact refinementPiece182_check
  · exact refinementPiece183_check
  · exact refinementPiece184_check
  · exact refinementPiece185_check
  · exact refinementPiece186_check
  · exact refinementPiece187_check
  · exact refinementPiece188_check
  · exact refinementPiece189_check
  · exact refinementPiece190_check
  · exact refinementPiece191_check
  · exact refinementPiece192_check
  · exact refinementPiece193_check
  · exact refinementPiece194_check
  · exact refinementPiece195_check
  · exact refinementPiece196_check
  · exact refinementPiece197_check
  · exact refinementPiece198_check
  · exact refinementPiece199_check
  · exact refinementPiece200_check
  · exact refinementPiece201_check
  · exact refinementPiece202_check
  · exact refinementPiece203_check
  · exact refinementPiece204_check
  · exact refinementPiece205_check
  · exact refinementPiece206_check
  · exact refinementPiece207_check
  · exact refinementPiece208_check
  · exact refinementPiece209_check
  · exact refinementPiece210_check
  · exact refinementPiece211_check
  · exact refinementPiece212_check
  · exact refinementPiece213_check
  · exact refinementPiece214_check
  · exact refinementPiece215_check

/-- Stable pieces 0..55 followed by the independently checked 216 refinements. -/
def improvedCatalog (i : Fin 272) : MacroPiece :=
  if h : i.val < 56 then stableMacroTable ⟨i.val, h⟩
  else refinementTable ⟨i.val - 56, by omega⟩


theorem improvedCatalog_check (i : Fin 272) : (improvedCatalog i).check = true := by
  unfold improvedCatalog
  split
  · exact stableMacroTable_check _
  · exact refinementTable_check _

#print axioms refinementTable_check
#print axioms improvedCatalog_check

end Zeta23.ThmD.Sextuple.MacroPrototype
