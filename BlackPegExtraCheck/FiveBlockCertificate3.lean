/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.FiveBlockCertificate3Cases0
import BlackPegExtraCheck.FiveBlockCertificate3Cases1
import BlackPegExtraCheck.FiveBlockCertificate3Cases2
import BlackPegExtraCheck.FiveBlockCertificate3Cases3
import BlackPegExtraCheck.FiveBlockCertificate3Cases4
import BlackPegExtraCheck.FiveBlockCertificate3Cases5
import BlackPegExtraCheck.FiveBlockCertificate3Cases6
import BlackPegExtraCheck.FiveBlockCertificate3Cases7
import BlackPegExtraCheck.FiveBlockCertificate3Cases8
import BlackPegExtraCheck.FiveBlockCertificate3Cases9
import BlackPegExtraCheck.FiveBlockCertificate3Cases10
import BlackPegExtraCheck.FiveBlockCertificate3Cases11
import BlackPegExtraCheck.FiveBlockCertificate3Cases12
import BlackPegExtraCheck.FiveBlockCertificate3Cases13
import BlackPegExtraCheck.FiveBlockCertificate3Cases14
import BlackPegExtraCheck.FiveBlockCertificate3Cases15
import BlackPegExtraCheck.FiveBlockCertificate3Cases16
import BlackPegExtraCheck.FiveBlockCertificate3Cases17
import BlackPegExtraCheck.FiveBlockCertificate3Cases18
import BlackPegExtraCheck.FiveBlockCertificate3Cases19
import BlackPegExtraCheck.FiveBlockCertificate3Cases20
import BlackPegExtraCheck.FiveBlockCertificate3Cases21
import BlackPegExtraCheck.FiveBlockCertificate3Cases22
import BlackPegExtraCheck.FiveBlockCertificate3Cases23
import BlackPegExtraCheck.FiveBlockCertificate3Cases24
import BlackPegExtraCheck.FiveBlockCertificate3Cases25
import BlackPegExtraCheck.FiveBlockCertificate3Cases26
import BlackPegExtraCheck.FiveBlockCertificate3Cases27
import BlackPegExtraCheck.FiveBlockCertificate3Cases28
import BlackPegExtraCheck.FiveBlockCertificate3Cases29
import BlackPegExtraCheck.FiveBlockCertificate3Cases30

namespace BlackPegExtraCheck

theorem fiveLevel3Transitions : ∀ node black bit,
    checkedBranch (fiveLevel3State node) (fiveLevel3Guess node) black
      (fiveLevel3Check node black) bit =
        fiveLevel4State (fiveLevel3Next node black bit) := by
  intro node
  change fiveLevel3TransitionAt node
  fin_cases node
  · exact fiveLevel3Transition_0
  · exact fiveLevel3Transition_1
  · exact fiveLevel3Transition_2
  · exact fiveLevel3Transition_3
  · exact fiveLevel3Transition_4
  · exact fiveLevel3Transition_5
  · exact fiveLevel3Transition_6
  · exact fiveLevel3Transition_7
  · exact fiveLevel3Transition_8
  · exact fiveLevel3Transition_9
  · exact fiveLevel3Transition_10
  · exact fiveLevel3Transition_11
  · exact fiveLevel3Transition_12
  · exact fiveLevel3Transition_13
  · exact fiveLevel3Transition_14
  · exact fiveLevel3Transition_15
  · exact fiveLevel3Transition_16
  · exact fiveLevel3Transition_17
  · exact fiveLevel3Transition_18
  · exact fiveLevel3Transition_19
  · exact fiveLevel3Transition_20
  · exact fiveLevel3Transition_21
  · exact fiveLevel3Transition_22
  · exact fiveLevel3Transition_23
  · exact fiveLevel3Transition_24
  · exact fiveLevel3Transition_25
  · exact fiveLevel3Transition_26
  · exact fiveLevel3Transition_27
  · exact fiveLevel3Transition_28
  · exact fiveLevel3Transition_29
  · exact fiveLevel3Transition_30
  · exact fiveLevel3Transition_31
  · exact fiveLevel3Transition_32
  · exact fiveLevel3Transition_33
  · exact fiveLevel3Transition_34
  · exact fiveLevel3Transition_35
  · exact fiveLevel3Transition_36
  · exact fiveLevel3Transition_37
  · exact fiveLevel3Transition_38
  · exact fiveLevel3Transition_39
  · exact fiveLevel3Transition_40
  · exact fiveLevel3Transition_41
  · exact fiveLevel3Transition_42
  · exact fiveLevel3Transition_43
  · exact fiveLevel3Transition_44
  · exact fiveLevel3Transition_45
  · exact fiveLevel3Transition_46
  · exact fiveLevel3Transition_47
  · exact fiveLevel3Transition_48
  · exact fiveLevel3Transition_49
  · exact fiveLevel3Transition_50
  · exact fiveLevel3Transition_51
  · exact fiveLevel3Transition_52
  · exact fiveLevel3Transition_53
  · exact fiveLevel3Transition_54
  · exact fiveLevel3Transition_55
  · exact fiveLevel3Transition_56
  · exact fiveLevel3Transition_57
  · exact fiveLevel3Transition_58
  · exact fiveLevel3Transition_59
  · exact fiveLevel3Transition_60
  · exact fiveLevel3Transition_61
  · exact fiveLevel3Transition_62
  · exact fiveLevel3Transition_63
  · exact fiveLevel3Transition_64
  · exact fiveLevel3Transition_65
  · exact fiveLevel3Transition_66
  · exact fiveLevel3Transition_67
  · exact fiveLevel3Transition_68
  · exact fiveLevel3Transition_69
  · exact fiveLevel3Transition_70
  · exact fiveLevel3Transition_71
  · exact fiveLevel3Transition_72
  · exact fiveLevel3Transition_73
  · exact fiveLevel3Transition_74
  · exact fiveLevel3Transition_75
  · exact fiveLevel3Transition_76
  · exact fiveLevel3Transition_77
  · exact fiveLevel3Transition_78
  · exact fiveLevel3Transition_79
  · exact fiveLevel3Transition_80
  · exact fiveLevel3Transition_81
  · exact fiveLevel3Transition_82
  · exact fiveLevel3Transition_83
  · exact fiveLevel3Transition_84
  · exact fiveLevel3Transition_85
  · exact fiveLevel3Transition_86
  · exact fiveLevel3Transition_87
  · exact fiveLevel3Transition_88
  · exact fiveLevel3Transition_89
  · exact fiveLevel3Transition_90
  · exact fiveLevel3Transition_91
  · exact fiveLevel3Transition_92
  · exact fiveLevel3Transition_93
  · exact fiveLevel3Transition_94
  · exact fiveLevel3Transition_95
  · exact fiveLevel3Transition_96
  · exact fiveLevel3Transition_97
  · exact fiveLevel3Transition_98
  · exact fiveLevel3Transition_99
  · exact fiveLevel3Transition_100
  · exact fiveLevel3Transition_101
  · exact fiveLevel3Transition_102
  · exact fiveLevel3Transition_103
  · exact fiveLevel3Transition_104
  · exact fiveLevel3Transition_105
  · exact fiveLevel3Transition_106
  · exact fiveLevel3Transition_107
  · exact fiveLevel3Transition_108
  · exact fiveLevel3Transition_109
  · exact fiveLevel3Transition_110
  · exact fiveLevel3Transition_111
  · exact fiveLevel3Transition_112
  · exact fiveLevel3Transition_113
  · exact fiveLevel3Transition_114
  · exact fiveLevel3Transition_115
  · exact fiveLevel3Transition_116
  · exact fiveLevel3Transition_117
  · exact fiveLevel3Transition_118
  · exact fiveLevel3Transition_119
  · exact fiveLevel3Transition_120
  · exact fiveLevel3Transition_121
  · exact fiveLevel3Transition_122
  · exact fiveLevel3Transition_123
  · exact fiveLevel3Transition_124
  · exact fiveLevel3Transition_125
  · exact fiveLevel3Transition_126
  · exact fiveLevel3Transition_127
  · exact fiveLevel3Transition_128
  · exact fiveLevel3Transition_129
  · exact fiveLevel3Transition_130
  · exact fiveLevel3Transition_131
  · exact fiveLevel3Transition_132
  · exact fiveLevel3Transition_133
  · exact fiveLevel3Transition_134
  · exact fiveLevel3Transition_135
  · exact fiveLevel3Transition_136
  · exact fiveLevel3Transition_137
  · exact fiveLevel3Transition_138
  · exact fiveLevel3Transition_139
  · exact fiveLevel3Transition_140
  · exact fiveLevel3Transition_141
  · exact fiveLevel3Transition_142
  · exact fiveLevel3Transition_143
  · exact fiveLevel3Transition_144
  · exact fiveLevel3Transition_145
  · exact fiveLevel3Transition_146
  · exact fiveLevel3Transition_147
  · exact fiveLevel3Transition_148
  · exact fiveLevel3Transition_149
  · exact fiveLevel3Transition_150
  · exact fiveLevel3Transition_151
  · exact fiveLevel3Transition_152
  · exact fiveLevel3Transition_153
  · exact fiveLevel3Transition_154
  · exact fiveLevel3Transition_155
  · exact fiveLevel3Transition_156
  · exact fiveLevel3Transition_157
  · exact fiveLevel3Transition_158
  · exact fiveLevel3Transition_159
  · exact fiveLevel3Transition_160
  · exact fiveLevel3Transition_161
  · exact fiveLevel3Transition_162
  · exact fiveLevel3Transition_163
  · exact fiveLevel3Transition_164
  · exact fiveLevel3Transition_165
  · exact fiveLevel3Transition_166
  · exact fiveLevel3Transition_167
  · exact fiveLevel3Transition_168
  · exact fiveLevel3Transition_169
  · exact fiveLevel3Transition_170
  · exact fiveLevel3Transition_171
  · exact fiveLevel3Transition_172
  · exact fiveLevel3Transition_173
  · exact fiveLevel3Transition_174
  · exact fiveLevel3Transition_175
  · exact fiveLevel3Transition_176
  · exact fiveLevel3Transition_177
  · exact fiveLevel3Transition_178
  · exact fiveLevel3Transition_179
  · exact fiveLevel3Transition_180
  · exact fiveLevel3Transition_181
  · exact fiveLevel3Transition_182
  · exact fiveLevel3Transition_183
  · exact fiveLevel3Transition_184
  · exact fiveLevel3Transition_185
  · exact fiveLevel3Transition_186
  · exact fiveLevel3Transition_187
  · exact fiveLevel3Transition_188
  · exact fiveLevel3Transition_189
  · exact fiveLevel3Transition_190
  · exact fiveLevel3Transition_191
  · exact fiveLevel3Transition_192
  · exact fiveLevel3Transition_193
  · exact fiveLevel3Transition_194
  · exact fiveLevel3Transition_195
  · exact fiveLevel3Transition_196
  · exact fiveLevel3Transition_197
  · exact fiveLevel3Transition_198
  · exact fiveLevel3Transition_199
  · exact fiveLevel3Transition_200
  · exact fiveLevel3Transition_201
  · exact fiveLevel3Transition_202
  · exact fiveLevel3Transition_203
  · exact fiveLevel3Transition_204
  · exact fiveLevel3Transition_205
  · exact fiveLevel3Transition_206
  · exact fiveLevel3Transition_207
  · exact fiveLevel3Transition_208
  · exact fiveLevel3Transition_209
  · exact fiveLevel3Transition_210
  · exact fiveLevel3Transition_211
  · exact fiveLevel3Transition_212
  · exact fiveLevel3Transition_213
  · exact fiveLevel3Transition_214
  · exact fiveLevel3Transition_215
  · exact fiveLevel3Transition_216
  · exact fiveLevel3Transition_217
  · exact fiveLevel3Transition_218
  · exact fiveLevel3Transition_219
  · exact fiveLevel3Transition_220
  · exact fiveLevel3Transition_221
  · exact fiveLevel3Transition_222
  · exact fiveLevel3Transition_223
  · exact fiveLevel3Transition_224
  · exact fiveLevel3Transition_225
  · exact fiveLevel3Transition_226
  · exact fiveLevel3Transition_227
  · exact fiveLevel3Transition_228
  · exact fiveLevel3Transition_229
  · exact fiveLevel3Transition_230
  · exact fiveLevel3Transition_231
  · exact fiveLevel3Transition_232
  · exact fiveLevel3Transition_233
  · exact fiveLevel3Transition_234
  · exact fiveLevel3Transition_235
  · exact fiveLevel3Transition_236
  · exact fiveLevel3Transition_237
  · exact fiveLevel3Transition_238
  · exact fiveLevel3Transition_239
  · exact fiveLevel3Transition_240
  · exact fiveLevel3Transition_241
  · exact fiveLevel3Transition_242

end BlackPegExtraCheck
