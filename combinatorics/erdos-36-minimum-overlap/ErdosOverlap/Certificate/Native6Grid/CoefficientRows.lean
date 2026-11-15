module

public import ErdosOverlap.Certificate.Native6Grid.Coefficients00
public import ErdosOverlap.Certificate.Native6Grid.Coefficients01
public import ErdosOverlap.Certificate.Native6Grid.Coefficients02
public import ErdosOverlap.Certificate.Native6Grid.Coefficients03
public import ErdosOverlap.Certificate.Native6Grid.Coefficients04
public import ErdosOverlap.Certificate.Native6Grid.Coefficients05
public import ErdosOverlap.Certificate.Native6Grid.Coefficients06
public import ErdosOverlap.Certificate.Native6Grid.Coefficients07
public import ErdosOverlap.Certificate.Native6Grid.Coefficients08
public import ErdosOverlap.Certificate.Native6Grid.Coefficients09
public import ErdosOverlap.Certificate.Native6Grid.Coefficients10
public import ErdosOverlap.Certificate.Native6Grid.Coefficients11
public import ErdosOverlap.Certificate.Native6Grid.Coefficients12
public import ErdosOverlap.Certificate.Native6Grid.Coefficients13
public import ErdosOverlap.Certificate.Native6Grid.Coefficients14
public import ErdosOverlap.Certificate.Native6Grid.Coefficients15

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

@[expose] def coefficientRow (j : ℕ) : List ℤ :=
  if j < 512 then
    if j < 256 then
      if j < 128 then
        if j < 64 then
          if j < 32 then
            if j < 16 then
              if j < 8 then
                if j < 4 then
                  if j < 2 then
                    if j < 1 then
                      coefficients0000
                    else
                      coefficients0001
                  else
                    if j < 3 then
                      coefficients0002
                    else
                      coefficients0003
                else
                  if j < 6 then
                    if j < 5 then
                      coefficients0004
                    else
                      coefficients0005
                  else
                    if j < 7 then
                      coefficients0006
                    else
                      coefficients0007
              else
                if j < 12 then
                  if j < 10 then
                    if j < 9 then
                      coefficients0008
                    else
                      coefficients0009
                  else
                    if j < 11 then
                      coefficients0010
                    else
                      coefficients0011
                else
                  if j < 14 then
                    if j < 13 then
                      coefficients0012
                    else
                      coefficients0013
                  else
                    if j < 15 then
                      coefficients0014
                    else
                      coefficients0015
            else
              if j < 24 then
                if j < 20 then
                  if j < 18 then
                    if j < 17 then
                      coefficients0016
                    else
                      coefficients0017
                  else
                    if j < 19 then
                      coefficients0018
                    else
                      coefficients0019
                else
                  if j < 22 then
                    if j < 21 then
                      coefficients0020
                    else
                      coefficients0021
                  else
                    if j < 23 then
                      coefficients0022
                    else
                      coefficients0023
              else
                if j < 28 then
                  if j < 26 then
                    if j < 25 then
                      coefficients0024
                    else
                      coefficients0025
                  else
                    if j < 27 then
                      coefficients0026
                    else
                      coefficients0027
                else
                  if j < 30 then
                    if j < 29 then
                      coefficients0028
                    else
                      coefficients0029
                  else
                    if j < 31 then
                      coefficients0030
                    else
                      coefficients0031
          else
            if j < 48 then
              if j < 40 then
                if j < 36 then
                  if j < 34 then
                    if j < 33 then
                      coefficients0032
                    else
                      coefficients0033
                  else
                    if j < 35 then
                      coefficients0034
                    else
                      coefficients0035
                else
                  if j < 38 then
                    if j < 37 then
                      coefficients0036
                    else
                      coefficients0037
                  else
                    if j < 39 then
                      coefficients0038
                    else
                      coefficients0039
              else
                if j < 44 then
                  if j < 42 then
                    if j < 41 then
                      coefficients0040
                    else
                      coefficients0041
                  else
                    if j < 43 then
                      coefficients0042
                    else
                      coefficients0043
                else
                  if j < 46 then
                    if j < 45 then
                      coefficients0044
                    else
                      coefficients0045
                  else
                    if j < 47 then
                      coefficients0046
                    else
                      coefficients0047
            else
              if j < 56 then
                if j < 52 then
                  if j < 50 then
                    if j < 49 then
                      coefficients0048
                    else
                      coefficients0049
                  else
                    if j < 51 then
                      coefficients0050
                    else
                      coefficients0051
                else
                  if j < 54 then
                    if j < 53 then
                      coefficients0052
                    else
                      coefficients0053
                  else
                    if j < 55 then
                      coefficients0054
                    else
                      coefficients0055
              else
                if j < 60 then
                  if j < 58 then
                    if j < 57 then
                      coefficients0056
                    else
                      coefficients0057
                  else
                    if j < 59 then
                      coefficients0058
                    else
                      coefficients0059
                else
                  if j < 62 then
                    if j < 61 then
                      coefficients0060
                    else
                      coefficients0061
                  else
                    if j < 63 then
                      coefficients0062
                    else
                      coefficients0063
        else
          if j < 96 then
            if j < 80 then
              if j < 72 then
                if j < 68 then
                  if j < 66 then
                    if j < 65 then
                      coefficients0064
                    else
                      coefficients0065
                  else
                    if j < 67 then
                      coefficients0066
                    else
                      coefficients0067
                else
                  if j < 70 then
                    if j < 69 then
                      coefficients0068
                    else
                      coefficients0069
                  else
                    if j < 71 then
                      coefficients0070
                    else
                      coefficients0071
              else
                if j < 76 then
                  if j < 74 then
                    if j < 73 then
                      coefficients0072
                    else
                      coefficients0073
                  else
                    if j < 75 then
                      coefficients0074
                    else
                      coefficients0075
                else
                  if j < 78 then
                    if j < 77 then
                      coefficients0076
                    else
                      coefficients0077
                  else
                    if j < 79 then
                      coefficients0078
                    else
                      coefficients0079
            else
              if j < 88 then
                if j < 84 then
                  if j < 82 then
                    if j < 81 then
                      coefficients0080
                    else
                      coefficients0081
                  else
                    if j < 83 then
                      coefficients0082
                    else
                      coefficients0083
                else
                  if j < 86 then
                    if j < 85 then
                      coefficients0084
                    else
                      coefficients0085
                  else
                    if j < 87 then
                      coefficients0086
                    else
                      coefficients0087
              else
                if j < 92 then
                  if j < 90 then
                    if j < 89 then
                      coefficients0088
                    else
                      coefficients0089
                  else
                    if j < 91 then
                      coefficients0090
                    else
                      coefficients0091
                else
                  if j < 94 then
                    if j < 93 then
                      coefficients0092
                    else
                      coefficients0093
                  else
                    if j < 95 then
                      coefficients0094
                    else
                      coefficients0095
          else
            if j < 112 then
              if j < 104 then
                if j < 100 then
                  if j < 98 then
                    if j < 97 then
                      coefficients0096
                    else
                      coefficients0097
                  else
                    if j < 99 then
                      coefficients0098
                    else
                      coefficients0099
                else
                  if j < 102 then
                    if j < 101 then
                      coefficients0100
                    else
                      coefficients0101
                  else
                    if j < 103 then
                      coefficients0102
                    else
                      coefficients0103
              else
                if j < 108 then
                  if j < 106 then
                    if j < 105 then
                      coefficients0104
                    else
                      coefficients0105
                  else
                    if j < 107 then
                      coefficients0106
                    else
                      coefficients0107
                else
                  if j < 110 then
                    if j < 109 then
                      coefficients0108
                    else
                      coefficients0109
                  else
                    if j < 111 then
                      coefficients0110
                    else
                      coefficients0111
            else
              if j < 120 then
                if j < 116 then
                  if j < 114 then
                    if j < 113 then
                      coefficients0112
                    else
                      coefficients0113
                  else
                    if j < 115 then
                      coefficients0114
                    else
                      coefficients0115
                else
                  if j < 118 then
                    if j < 117 then
                      coefficients0116
                    else
                      coefficients0117
                  else
                    if j < 119 then
                      coefficients0118
                    else
                      coefficients0119
              else
                if j < 124 then
                  if j < 122 then
                    if j < 121 then
                      coefficients0120
                    else
                      coefficients0121
                  else
                    if j < 123 then
                      coefficients0122
                    else
                      coefficients0123
                else
                  if j < 126 then
                    if j < 125 then
                      coefficients0124
                    else
                      coefficients0125
                  else
                    if j < 127 then
                      coefficients0126
                    else
                      coefficients0127
      else
        if j < 192 then
          if j < 160 then
            if j < 144 then
              if j < 136 then
                if j < 132 then
                  if j < 130 then
                    if j < 129 then
                      coefficients0128
                    else
                      coefficients0129
                  else
                    if j < 131 then
                      coefficients0130
                    else
                      coefficients0131
                else
                  if j < 134 then
                    if j < 133 then
                      coefficients0132
                    else
                      coefficients0133
                  else
                    if j < 135 then
                      coefficients0134
                    else
                      coefficients0135
              else
                if j < 140 then
                  if j < 138 then
                    if j < 137 then
                      coefficients0136
                    else
                      coefficients0137
                  else
                    if j < 139 then
                      coefficients0138
                    else
                      coefficients0139
                else
                  if j < 142 then
                    if j < 141 then
                      coefficients0140
                    else
                      coefficients0141
                  else
                    if j < 143 then
                      coefficients0142
                    else
                      coefficients0143
            else
              if j < 152 then
                if j < 148 then
                  if j < 146 then
                    if j < 145 then
                      coefficients0144
                    else
                      coefficients0145
                  else
                    if j < 147 then
                      coefficients0146
                    else
                      coefficients0147
                else
                  if j < 150 then
                    if j < 149 then
                      coefficients0148
                    else
                      coefficients0149
                  else
                    if j < 151 then
                      coefficients0150
                    else
                      coefficients0151
              else
                if j < 156 then
                  if j < 154 then
                    if j < 153 then
                      coefficients0152
                    else
                      coefficients0153
                  else
                    if j < 155 then
                      coefficients0154
                    else
                      coefficients0155
                else
                  if j < 158 then
                    if j < 157 then
                      coefficients0156
                    else
                      coefficients0157
                  else
                    if j < 159 then
                      coefficients0158
                    else
                      coefficients0159
          else
            if j < 176 then
              if j < 168 then
                if j < 164 then
                  if j < 162 then
                    if j < 161 then
                      coefficients0160
                    else
                      coefficients0161
                  else
                    if j < 163 then
                      coefficients0162
                    else
                      coefficients0163
                else
                  if j < 166 then
                    if j < 165 then
                      coefficients0164
                    else
                      coefficients0165
                  else
                    if j < 167 then
                      coefficients0166
                    else
                      coefficients0167
              else
                if j < 172 then
                  if j < 170 then
                    if j < 169 then
                      coefficients0168
                    else
                      coefficients0169
                  else
                    if j < 171 then
                      coefficients0170
                    else
                      coefficients0171
                else
                  if j < 174 then
                    if j < 173 then
                      coefficients0172
                    else
                      coefficients0173
                  else
                    if j < 175 then
                      coefficients0174
                    else
                      coefficients0175
            else
              if j < 184 then
                if j < 180 then
                  if j < 178 then
                    if j < 177 then
                      coefficients0176
                    else
                      coefficients0177
                  else
                    if j < 179 then
                      coefficients0178
                    else
                      coefficients0179
                else
                  if j < 182 then
                    if j < 181 then
                      coefficients0180
                    else
                      coefficients0181
                  else
                    if j < 183 then
                      coefficients0182
                    else
                      coefficients0183
              else
                if j < 188 then
                  if j < 186 then
                    if j < 185 then
                      coefficients0184
                    else
                      coefficients0185
                  else
                    if j < 187 then
                      coefficients0186
                    else
                      coefficients0187
                else
                  if j < 190 then
                    if j < 189 then
                      coefficients0188
                    else
                      coefficients0189
                  else
                    if j < 191 then
                      coefficients0190
                    else
                      coefficients0191
        else
          if j < 224 then
            if j < 208 then
              if j < 200 then
                if j < 196 then
                  if j < 194 then
                    if j < 193 then
                      coefficients0192
                    else
                      coefficients0193
                  else
                    if j < 195 then
                      coefficients0194
                    else
                      coefficients0195
                else
                  if j < 198 then
                    if j < 197 then
                      coefficients0196
                    else
                      coefficients0197
                  else
                    if j < 199 then
                      coefficients0198
                    else
                      coefficients0199
              else
                if j < 204 then
                  if j < 202 then
                    if j < 201 then
                      coefficients0200
                    else
                      coefficients0201
                  else
                    if j < 203 then
                      coefficients0202
                    else
                      coefficients0203
                else
                  if j < 206 then
                    if j < 205 then
                      coefficients0204
                    else
                      coefficients0205
                  else
                    if j < 207 then
                      coefficients0206
                    else
                      coefficients0207
            else
              if j < 216 then
                if j < 212 then
                  if j < 210 then
                    if j < 209 then
                      coefficients0208
                    else
                      coefficients0209
                  else
                    if j < 211 then
                      coefficients0210
                    else
                      coefficients0211
                else
                  if j < 214 then
                    if j < 213 then
                      coefficients0212
                    else
                      coefficients0213
                  else
                    if j < 215 then
                      coefficients0214
                    else
                      coefficients0215
              else
                if j < 220 then
                  if j < 218 then
                    if j < 217 then
                      coefficients0216
                    else
                      coefficients0217
                  else
                    if j < 219 then
                      coefficients0218
                    else
                      coefficients0219
                else
                  if j < 222 then
                    if j < 221 then
                      coefficients0220
                    else
                      coefficients0221
                  else
                    if j < 223 then
                      coefficients0222
                    else
                      coefficients0223
          else
            if j < 240 then
              if j < 232 then
                if j < 228 then
                  if j < 226 then
                    if j < 225 then
                      coefficients0224
                    else
                      coefficients0225
                  else
                    if j < 227 then
                      coefficients0226
                    else
                      coefficients0227
                else
                  if j < 230 then
                    if j < 229 then
                      coefficients0228
                    else
                      coefficients0229
                  else
                    if j < 231 then
                      coefficients0230
                    else
                      coefficients0231
              else
                if j < 236 then
                  if j < 234 then
                    if j < 233 then
                      coefficients0232
                    else
                      coefficients0233
                  else
                    if j < 235 then
                      coefficients0234
                    else
                      coefficients0235
                else
                  if j < 238 then
                    if j < 237 then
                      coefficients0236
                    else
                      coefficients0237
                  else
                    if j < 239 then
                      coefficients0238
                    else
                      coefficients0239
            else
              if j < 248 then
                if j < 244 then
                  if j < 242 then
                    if j < 241 then
                      coefficients0240
                    else
                      coefficients0241
                  else
                    if j < 243 then
                      coefficients0242
                    else
                      coefficients0243
                else
                  if j < 246 then
                    if j < 245 then
                      coefficients0244
                    else
                      coefficients0245
                  else
                    if j < 247 then
                      coefficients0246
                    else
                      coefficients0247
              else
                if j < 252 then
                  if j < 250 then
                    if j < 249 then
                      coefficients0248
                    else
                      coefficients0249
                  else
                    if j < 251 then
                      coefficients0250
                    else
                      coefficients0251
                else
                  if j < 254 then
                    if j < 253 then
                      coefficients0252
                    else
                      coefficients0253
                  else
                    if j < 255 then
                      coefficients0254
                    else
                      coefficients0255
    else
      if j < 384 then
        if j < 320 then
          if j < 288 then
            if j < 272 then
              if j < 264 then
                if j < 260 then
                  if j < 258 then
                    if j < 257 then
                      coefficients0256
                    else
                      coefficients0257
                  else
                    if j < 259 then
                      coefficients0258
                    else
                      coefficients0259
                else
                  if j < 262 then
                    if j < 261 then
                      coefficients0260
                    else
                      coefficients0261
                  else
                    if j < 263 then
                      coefficients0262
                    else
                      coefficients0263
              else
                if j < 268 then
                  if j < 266 then
                    if j < 265 then
                      coefficients0264
                    else
                      coefficients0265
                  else
                    if j < 267 then
                      coefficients0266
                    else
                      coefficients0267
                else
                  if j < 270 then
                    if j < 269 then
                      coefficients0268
                    else
                      coefficients0269
                  else
                    if j < 271 then
                      coefficients0270
                    else
                      coefficients0271
            else
              if j < 280 then
                if j < 276 then
                  if j < 274 then
                    if j < 273 then
                      coefficients0272
                    else
                      coefficients0273
                  else
                    if j < 275 then
                      coefficients0274
                    else
                      coefficients0275
                else
                  if j < 278 then
                    if j < 277 then
                      coefficients0276
                    else
                      coefficients0277
                  else
                    if j < 279 then
                      coefficients0278
                    else
                      coefficients0279
              else
                if j < 284 then
                  if j < 282 then
                    if j < 281 then
                      coefficients0280
                    else
                      coefficients0281
                  else
                    if j < 283 then
                      coefficients0282
                    else
                      coefficients0283
                else
                  if j < 286 then
                    if j < 285 then
                      coefficients0284
                    else
                      coefficients0285
                  else
                    if j < 287 then
                      coefficients0286
                    else
                      coefficients0287
          else
            if j < 304 then
              if j < 296 then
                if j < 292 then
                  if j < 290 then
                    if j < 289 then
                      coefficients0288
                    else
                      coefficients0289
                  else
                    if j < 291 then
                      coefficients0290
                    else
                      coefficients0291
                else
                  if j < 294 then
                    if j < 293 then
                      coefficients0292
                    else
                      coefficients0293
                  else
                    if j < 295 then
                      coefficients0294
                    else
                      coefficients0295
              else
                if j < 300 then
                  if j < 298 then
                    if j < 297 then
                      coefficients0296
                    else
                      coefficients0297
                  else
                    if j < 299 then
                      coefficients0298
                    else
                      coefficients0299
                else
                  if j < 302 then
                    if j < 301 then
                      coefficients0300
                    else
                      coefficients0301
                  else
                    if j < 303 then
                      coefficients0302
                    else
                      coefficients0303
            else
              if j < 312 then
                if j < 308 then
                  if j < 306 then
                    if j < 305 then
                      coefficients0304
                    else
                      coefficients0305
                  else
                    if j < 307 then
                      coefficients0306
                    else
                      coefficients0307
                else
                  if j < 310 then
                    if j < 309 then
                      coefficients0308
                    else
                      coefficients0309
                  else
                    if j < 311 then
                      coefficients0310
                    else
                      coefficients0311
              else
                if j < 316 then
                  if j < 314 then
                    if j < 313 then
                      coefficients0312
                    else
                      coefficients0313
                  else
                    if j < 315 then
                      coefficients0314
                    else
                      coefficients0315
                else
                  if j < 318 then
                    if j < 317 then
                      coefficients0316
                    else
                      coefficients0317
                  else
                    if j < 319 then
                      coefficients0318
                    else
                      coefficients0319
        else
          if j < 352 then
            if j < 336 then
              if j < 328 then
                if j < 324 then
                  if j < 322 then
                    if j < 321 then
                      coefficients0320
                    else
                      coefficients0321
                  else
                    if j < 323 then
                      coefficients0322
                    else
                      coefficients0323
                else
                  if j < 326 then
                    if j < 325 then
                      coefficients0324
                    else
                      coefficients0325
                  else
                    if j < 327 then
                      coefficients0326
                    else
                      coefficients0327
              else
                if j < 332 then
                  if j < 330 then
                    if j < 329 then
                      coefficients0328
                    else
                      coefficients0329
                  else
                    if j < 331 then
                      coefficients0330
                    else
                      coefficients0331
                else
                  if j < 334 then
                    if j < 333 then
                      coefficients0332
                    else
                      coefficients0333
                  else
                    if j < 335 then
                      coefficients0334
                    else
                      coefficients0335
            else
              if j < 344 then
                if j < 340 then
                  if j < 338 then
                    if j < 337 then
                      coefficients0336
                    else
                      coefficients0337
                  else
                    if j < 339 then
                      coefficients0338
                    else
                      coefficients0339
                else
                  if j < 342 then
                    if j < 341 then
                      coefficients0340
                    else
                      coefficients0341
                  else
                    if j < 343 then
                      coefficients0342
                    else
                      coefficients0343
              else
                if j < 348 then
                  if j < 346 then
                    if j < 345 then
                      coefficients0344
                    else
                      coefficients0345
                  else
                    if j < 347 then
                      coefficients0346
                    else
                      coefficients0347
                else
                  if j < 350 then
                    if j < 349 then
                      coefficients0348
                    else
                      coefficients0349
                  else
                    if j < 351 then
                      coefficients0350
                    else
                      coefficients0351
          else
            if j < 368 then
              if j < 360 then
                if j < 356 then
                  if j < 354 then
                    if j < 353 then
                      coefficients0352
                    else
                      coefficients0353
                  else
                    if j < 355 then
                      coefficients0354
                    else
                      coefficients0355
                else
                  if j < 358 then
                    if j < 357 then
                      coefficients0356
                    else
                      coefficients0357
                  else
                    if j < 359 then
                      coefficients0358
                    else
                      coefficients0359
              else
                if j < 364 then
                  if j < 362 then
                    if j < 361 then
                      coefficients0360
                    else
                      coefficients0361
                  else
                    if j < 363 then
                      coefficients0362
                    else
                      coefficients0363
                else
                  if j < 366 then
                    if j < 365 then
                      coefficients0364
                    else
                      coefficients0365
                  else
                    if j < 367 then
                      coefficients0366
                    else
                      coefficients0367
            else
              if j < 376 then
                if j < 372 then
                  if j < 370 then
                    if j < 369 then
                      coefficients0368
                    else
                      coefficients0369
                  else
                    if j < 371 then
                      coefficients0370
                    else
                      coefficients0371
                else
                  if j < 374 then
                    if j < 373 then
                      coefficients0372
                    else
                      coefficients0373
                  else
                    if j < 375 then
                      coefficients0374
                    else
                      coefficients0375
              else
                if j < 380 then
                  if j < 378 then
                    if j < 377 then
                      coefficients0376
                    else
                      coefficients0377
                  else
                    if j < 379 then
                      coefficients0378
                    else
                      coefficients0379
                else
                  if j < 382 then
                    if j < 381 then
                      coefficients0380
                    else
                      coefficients0381
                  else
                    if j < 383 then
                      coefficients0382
                    else
                      coefficients0383
      else
        if j < 448 then
          if j < 416 then
            if j < 400 then
              if j < 392 then
                if j < 388 then
                  if j < 386 then
                    if j < 385 then
                      coefficients0384
                    else
                      coefficients0385
                  else
                    if j < 387 then
                      coefficients0386
                    else
                      coefficients0387
                else
                  if j < 390 then
                    if j < 389 then
                      coefficients0388
                    else
                      coefficients0389
                  else
                    if j < 391 then
                      coefficients0390
                    else
                      coefficients0391
              else
                if j < 396 then
                  if j < 394 then
                    if j < 393 then
                      coefficients0392
                    else
                      coefficients0393
                  else
                    if j < 395 then
                      coefficients0394
                    else
                      coefficients0395
                else
                  if j < 398 then
                    if j < 397 then
                      coefficients0396
                    else
                      coefficients0397
                  else
                    if j < 399 then
                      coefficients0398
                    else
                      coefficients0399
            else
              if j < 408 then
                if j < 404 then
                  if j < 402 then
                    if j < 401 then
                      coefficients0400
                    else
                      coefficients0401
                  else
                    if j < 403 then
                      coefficients0402
                    else
                      coefficients0403
                else
                  if j < 406 then
                    if j < 405 then
                      coefficients0404
                    else
                      coefficients0405
                  else
                    if j < 407 then
                      coefficients0406
                    else
                      coefficients0407
              else
                if j < 412 then
                  if j < 410 then
                    if j < 409 then
                      coefficients0408
                    else
                      coefficients0409
                  else
                    if j < 411 then
                      coefficients0410
                    else
                      coefficients0411
                else
                  if j < 414 then
                    if j < 413 then
                      coefficients0412
                    else
                      coefficients0413
                  else
                    if j < 415 then
                      coefficients0414
                    else
                      coefficients0415
          else
            if j < 432 then
              if j < 424 then
                if j < 420 then
                  if j < 418 then
                    if j < 417 then
                      coefficients0416
                    else
                      coefficients0417
                  else
                    if j < 419 then
                      coefficients0418
                    else
                      coefficients0419
                else
                  if j < 422 then
                    if j < 421 then
                      coefficients0420
                    else
                      coefficients0421
                  else
                    if j < 423 then
                      coefficients0422
                    else
                      coefficients0423
              else
                if j < 428 then
                  if j < 426 then
                    if j < 425 then
                      coefficients0424
                    else
                      coefficients0425
                  else
                    if j < 427 then
                      coefficients0426
                    else
                      coefficients0427
                else
                  if j < 430 then
                    if j < 429 then
                      coefficients0428
                    else
                      coefficients0429
                  else
                    if j < 431 then
                      coefficients0430
                    else
                      coefficients0431
            else
              if j < 440 then
                if j < 436 then
                  if j < 434 then
                    if j < 433 then
                      coefficients0432
                    else
                      coefficients0433
                  else
                    if j < 435 then
                      coefficients0434
                    else
                      coefficients0435
                else
                  if j < 438 then
                    if j < 437 then
                      coefficients0436
                    else
                      coefficients0437
                  else
                    if j < 439 then
                      coefficients0438
                    else
                      coefficients0439
              else
                if j < 444 then
                  if j < 442 then
                    if j < 441 then
                      coefficients0440
                    else
                      coefficients0441
                  else
                    if j < 443 then
                      coefficients0442
                    else
                      coefficients0443
                else
                  if j < 446 then
                    if j < 445 then
                      coefficients0444
                    else
                      coefficients0445
                  else
                    if j < 447 then
                      coefficients0446
                    else
                      coefficients0447
        else
          if j < 480 then
            if j < 464 then
              if j < 456 then
                if j < 452 then
                  if j < 450 then
                    if j < 449 then
                      coefficients0448
                    else
                      coefficients0449
                  else
                    if j < 451 then
                      coefficients0450
                    else
                      coefficients0451
                else
                  if j < 454 then
                    if j < 453 then
                      coefficients0452
                    else
                      coefficients0453
                  else
                    if j < 455 then
                      coefficients0454
                    else
                      coefficients0455
              else
                if j < 460 then
                  if j < 458 then
                    if j < 457 then
                      coefficients0456
                    else
                      coefficients0457
                  else
                    if j < 459 then
                      coefficients0458
                    else
                      coefficients0459
                else
                  if j < 462 then
                    if j < 461 then
                      coefficients0460
                    else
                      coefficients0461
                  else
                    if j < 463 then
                      coefficients0462
                    else
                      coefficients0463
            else
              if j < 472 then
                if j < 468 then
                  if j < 466 then
                    if j < 465 then
                      coefficients0464
                    else
                      coefficients0465
                  else
                    if j < 467 then
                      coefficients0466
                    else
                      coefficients0467
                else
                  if j < 470 then
                    if j < 469 then
                      coefficients0468
                    else
                      coefficients0469
                  else
                    if j < 471 then
                      coefficients0470
                    else
                      coefficients0471
              else
                if j < 476 then
                  if j < 474 then
                    if j < 473 then
                      coefficients0472
                    else
                      coefficients0473
                  else
                    if j < 475 then
                      coefficients0474
                    else
                      coefficients0475
                else
                  if j < 478 then
                    if j < 477 then
                      coefficients0476
                    else
                      coefficients0477
                  else
                    if j < 479 then
                      coefficients0478
                    else
                      coefficients0479
          else
            if j < 496 then
              if j < 488 then
                if j < 484 then
                  if j < 482 then
                    if j < 481 then
                      coefficients0480
                    else
                      coefficients0481
                  else
                    if j < 483 then
                      coefficients0482
                    else
                      coefficients0483
                else
                  if j < 486 then
                    if j < 485 then
                      coefficients0484
                    else
                      coefficients0485
                  else
                    if j < 487 then
                      coefficients0486
                    else
                      coefficients0487
              else
                if j < 492 then
                  if j < 490 then
                    if j < 489 then
                      coefficients0488
                    else
                      coefficients0489
                  else
                    if j < 491 then
                      coefficients0490
                    else
                      coefficients0491
                else
                  if j < 494 then
                    if j < 493 then
                      coefficients0492
                    else
                      coefficients0493
                  else
                    if j < 495 then
                      coefficients0494
                    else
                      coefficients0495
            else
              if j < 504 then
                if j < 500 then
                  if j < 498 then
                    if j < 497 then
                      coefficients0496
                    else
                      coefficients0497
                  else
                    if j < 499 then
                      coefficients0498
                    else
                      coefficients0499
                else
                  if j < 502 then
                    if j < 501 then
                      coefficients0500
                    else
                      coefficients0501
                  else
                    if j < 503 then
                      coefficients0502
                    else
                      coefficients0503
              else
                if j < 508 then
                  if j < 506 then
                    if j < 505 then
                      coefficients0504
                    else
                      coefficients0505
                  else
                    if j < 507 then
                      coefficients0506
                    else
                      coefficients0507
                else
                  if j < 510 then
                    if j < 509 then
                      coefficients0508
                    else
                      coefficients0509
                  else
                    if j < 511 then
                      coefficients0510
                    else
                      coefficients0511
  else
    if j < 768 then
      if j < 640 then
        if j < 576 then
          if j < 544 then
            if j < 528 then
              if j < 520 then
                if j < 516 then
                  if j < 514 then
                    if j < 513 then
                      coefficients0512
                    else
                      coefficients0513
                  else
                    if j < 515 then
                      coefficients0514
                    else
                      coefficients0515
                else
                  if j < 518 then
                    if j < 517 then
                      coefficients0516
                    else
                      coefficients0517
                  else
                    if j < 519 then
                      coefficients0518
                    else
                      coefficients0519
              else
                if j < 524 then
                  if j < 522 then
                    if j < 521 then
                      coefficients0520
                    else
                      coefficients0521
                  else
                    if j < 523 then
                      coefficients0522
                    else
                      coefficients0523
                else
                  if j < 526 then
                    if j < 525 then
                      coefficients0524
                    else
                      coefficients0525
                  else
                    if j < 527 then
                      coefficients0526
                    else
                      coefficients0527
            else
              if j < 536 then
                if j < 532 then
                  if j < 530 then
                    if j < 529 then
                      coefficients0528
                    else
                      coefficients0529
                  else
                    if j < 531 then
                      coefficients0530
                    else
                      coefficients0531
                else
                  if j < 534 then
                    if j < 533 then
                      coefficients0532
                    else
                      coefficients0533
                  else
                    if j < 535 then
                      coefficients0534
                    else
                      coefficients0535
              else
                if j < 540 then
                  if j < 538 then
                    if j < 537 then
                      coefficients0536
                    else
                      coefficients0537
                  else
                    if j < 539 then
                      coefficients0538
                    else
                      coefficients0539
                else
                  if j < 542 then
                    if j < 541 then
                      coefficients0540
                    else
                      coefficients0541
                  else
                    if j < 543 then
                      coefficients0542
                    else
                      coefficients0543
          else
            if j < 560 then
              if j < 552 then
                if j < 548 then
                  if j < 546 then
                    if j < 545 then
                      coefficients0544
                    else
                      coefficients0545
                  else
                    if j < 547 then
                      coefficients0546
                    else
                      coefficients0547
                else
                  if j < 550 then
                    if j < 549 then
                      coefficients0548
                    else
                      coefficients0549
                  else
                    if j < 551 then
                      coefficients0550
                    else
                      coefficients0551
              else
                if j < 556 then
                  if j < 554 then
                    if j < 553 then
                      coefficients0552
                    else
                      coefficients0553
                  else
                    if j < 555 then
                      coefficients0554
                    else
                      coefficients0555
                else
                  if j < 558 then
                    if j < 557 then
                      coefficients0556
                    else
                      coefficients0557
                  else
                    if j < 559 then
                      coefficients0558
                    else
                      coefficients0559
            else
              if j < 568 then
                if j < 564 then
                  if j < 562 then
                    if j < 561 then
                      coefficients0560
                    else
                      coefficients0561
                  else
                    if j < 563 then
                      coefficients0562
                    else
                      coefficients0563
                else
                  if j < 566 then
                    if j < 565 then
                      coefficients0564
                    else
                      coefficients0565
                  else
                    if j < 567 then
                      coefficients0566
                    else
                      coefficients0567
              else
                if j < 572 then
                  if j < 570 then
                    if j < 569 then
                      coefficients0568
                    else
                      coefficients0569
                  else
                    if j < 571 then
                      coefficients0570
                    else
                      coefficients0571
                else
                  if j < 574 then
                    if j < 573 then
                      coefficients0572
                    else
                      coefficients0573
                  else
                    if j < 575 then
                      coefficients0574
                    else
                      coefficients0575
        else
          if j < 608 then
            if j < 592 then
              if j < 584 then
                if j < 580 then
                  if j < 578 then
                    if j < 577 then
                      coefficients0576
                    else
                      coefficients0577
                  else
                    if j < 579 then
                      coefficients0578
                    else
                      coefficients0579
                else
                  if j < 582 then
                    if j < 581 then
                      coefficients0580
                    else
                      coefficients0581
                  else
                    if j < 583 then
                      coefficients0582
                    else
                      coefficients0583
              else
                if j < 588 then
                  if j < 586 then
                    if j < 585 then
                      coefficients0584
                    else
                      coefficients0585
                  else
                    if j < 587 then
                      coefficients0586
                    else
                      coefficients0587
                else
                  if j < 590 then
                    if j < 589 then
                      coefficients0588
                    else
                      coefficients0589
                  else
                    if j < 591 then
                      coefficients0590
                    else
                      coefficients0591
            else
              if j < 600 then
                if j < 596 then
                  if j < 594 then
                    if j < 593 then
                      coefficients0592
                    else
                      coefficients0593
                  else
                    if j < 595 then
                      coefficients0594
                    else
                      coefficients0595
                else
                  if j < 598 then
                    if j < 597 then
                      coefficients0596
                    else
                      coefficients0597
                  else
                    if j < 599 then
                      coefficients0598
                    else
                      coefficients0599
              else
                if j < 604 then
                  if j < 602 then
                    if j < 601 then
                      coefficients0600
                    else
                      coefficients0601
                  else
                    if j < 603 then
                      coefficients0602
                    else
                      coefficients0603
                else
                  if j < 606 then
                    if j < 605 then
                      coefficients0604
                    else
                      coefficients0605
                  else
                    if j < 607 then
                      coefficients0606
                    else
                      coefficients0607
          else
            if j < 624 then
              if j < 616 then
                if j < 612 then
                  if j < 610 then
                    if j < 609 then
                      coefficients0608
                    else
                      coefficients0609
                  else
                    if j < 611 then
                      coefficients0610
                    else
                      coefficients0611
                else
                  if j < 614 then
                    if j < 613 then
                      coefficients0612
                    else
                      coefficients0613
                  else
                    if j < 615 then
                      coefficients0614
                    else
                      coefficients0615
              else
                if j < 620 then
                  if j < 618 then
                    if j < 617 then
                      coefficients0616
                    else
                      coefficients0617
                  else
                    if j < 619 then
                      coefficients0618
                    else
                      coefficients0619
                else
                  if j < 622 then
                    if j < 621 then
                      coefficients0620
                    else
                      coefficients0621
                  else
                    if j < 623 then
                      coefficients0622
                    else
                      coefficients0623
            else
              if j < 632 then
                if j < 628 then
                  if j < 626 then
                    if j < 625 then
                      coefficients0624
                    else
                      coefficients0625
                  else
                    if j < 627 then
                      coefficients0626
                    else
                      coefficients0627
                else
                  if j < 630 then
                    if j < 629 then
                      coefficients0628
                    else
                      coefficients0629
                  else
                    if j < 631 then
                      coefficients0630
                    else
                      coefficients0631
              else
                if j < 636 then
                  if j < 634 then
                    if j < 633 then
                      coefficients0632
                    else
                      coefficients0633
                  else
                    if j < 635 then
                      coefficients0634
                    else
                      coefficients0635
                else
                  if j < 638 then
                    if j < 637 then
                      coefficients0636
                    else
                      coefficients0637
                  else
                    if j < 639 then
                      coefficients0638
                    else
                      coefficients0639
      else
        if j < 704 then
          if j < 672 then
            if j < 656 then
              if j < 648 then
                if j < 644 then
                  if j < 642 then
                    if j < 641 then
                      coefficients0640
                    else
                      coefficients0641
                  else
                    if j < 643 then
                      coefficients0642
                    else
                      coefficients0643
                else
                  if j < 646 then
                    if j < 645 then
                      coefficients0644
                    else
                      coefficients0645
                  else
                    if j < 647 then
                      coefficients0646
                    else
                      coefficients0647
              else
                if j < 652 then
                  if j < 650 then
                    if j < 649 then
                      coefficients0648
                    else
                      coefficients0649
                  else
                    if j < 651 then
                      coefficients0650
                    else
                      coefficients0651
                else
                  if j < 654 then
                    if j < 653 then
                      coefficients0652
                    else
                      coefficients0653
                  else
                    if j < 655 then
                      coefficients0654
                    else
                      coefficients0655
            else
              if j < 664 then
                if j < 660 then
                  if j < 658 then
                    if j < 657 then
                      coefficients0656
                    else
                      coefficients0657
                  else
                    if j < 659 then
                      coefficients0658
                    else
                      coefficients0659
                else
                  if j < 662 then
                    if j < 661 then
                      coefficients0660
                    else
                      coefficients0661
                  else
                    if j < 663 then
                      coefficients0662
                    else
                      coefficients0663
              else
                if j < 668 then
                  if j < 666 then
                    if j < 665 then
                      coefficients0664
                    else
                      coefficients0665
                  else
                    if j < 667 then
                      coefficients0666
                    else
                      coefficients0667
                else
                  if j < 670 then
                    if j < 669 then
                      coefficients0668
                    else
                      coefficients0669
                  else
                    if j < 671 then
                      coefficients0670
                    else
                      coefficients0671
          else
            if j < 688 then
              if j < 680 then
                if j < 676 then
                  if j < 674 then
                    if j < 673 then
                      coefficients0672
                    else
                      coefficients0673
                  else
                    if j < 675 then
                      coefficients0674
                    else
                      coefficients0675
                else
                  if j < 678 then
                    if j < 677 then
                      coefficients0676
                    else
                      coefficients0677
                  else
                    if j < 679 then
                      coefficients0678
                    else
                      coefficients0679
              else
                if j < 684 then
                  if j < 682 then
                    if j < 681 then
                      coefficients0680
                    else
                      coefficients0681
                  else
                    if j < 683 then
                      coefficients0682
                    else
                      coefficients0683
                else
                  if j < 686 then
                    if j < 685 then
                      coefficients0684
                    else
                      coefficients0685
                  else
                    if j < 687 then
                      coefficients0686
                    else
                      coefficients0687
            else
              if j < 696 then
                if j < 692 then
                  if j < 690 then
                    if j < 689 then
                      coefficients0688
                    else
                      coefficients0689
                  else
                    if j < 691 then
                      coefficients0690
                    else
                      coefficients0691
                else
                  if j < 694 then
                    if j < 693 then
                      coefficients0692
                    else
                      coefficients0693
                  else
                    if j < 695 then
                      coefficients0694
                    else
                      coefficients0695
              else
                if j < 700 then
                  if j < 698 then
                    if j < 697 then
                      coefficients0696
                    else
                      coefficients0697
                  else
                    if j < 699 then
                      coefficients0698
                    else
                      coefficients0699
                else
                  if j < 702 then
                    if j < 701 then
                      coefficients0700
                    else
                      coefficients0701
                  else
                    if j < 703 then
                      coefficients0702
                    else
                      coefficients0703
        else
          if j < 736 then
            if j < 720 then
              if j < 712 then
                if j < 708 then
                  if j < 706 then
                    if j < 705 then
                      coefficients0704
                    else
                      coefficients0705
                  else
                    if j < 707 then
                      coefficients0706
                    else
                      coefficients0707
                else
                  if j < 710 then
                    if j < 709 then
                      coefficients0708
                    else
                      coefficients0709
                  else
                    if j < 711 then
                      coefficients0710
                    else
                      coefficients0711
              else
                if j < 716 then
                  if j < 714 then
                    if j < 713 then
                      coefficients0712
                    else
                      coefficients0713
                  else
                    if j < 715 then
                      coefficients0714
                    else
                      coefficients0715
                else
                  if j < 718 then
                    if j < 717 then
                      coefficients0716
                    else
                      coefficients0717
                  else
                    if j < 719 then
                      coefficients0718
                    else
                      coefficients0719
            else
              if j < 728 then
                if j < 724 then
                  if j < 722 then
                    if j < 721 then
                      coefficients0720
                    else
                      coefficients0721
                  else
                    if j < 723 then
                      coefficients0722
                    else
                      coefficients0723
                else
                  if j < 726 then
                    if j < 725 then
                      coefficients0724
                    else
                      coefficients0725
                  else
                    if j < 727 then
                      coefficients0726
                    else
                      coefficients0727
              else
                if j < 732 then
                  if j < 730 then
                    if j < 729 then
                      coefficients0728
                    else
                      coefficients0729
                  else
                    if j < 731 then
                      coefficients0730
                    else
                      coefficients0731
                else
                  if j < 734 then
                    if j < 733 then
                      coefficients0732
                    else
                      coefficients0733
                  else
                    if j < 735 then
                      coefficients0734
                    else
                      coefficients0735
          else
            if j < 752 then
              if j < 744 then
                if j < 740 then
                  if j < 738 then
                    if j < 737 then
                      coefficients0736
                    else
                      coefficients0737
                  else
                    if j < 739 then
                      coefficients0738
                    else
                      coefficients0739
                else
                  if j < 742 then
                    if j < 741 then
                      coefficients0740
                    else
                      coefficients0741
                  else
                    if j < 743 then
                      coefficients0742
                    else
                      coefficients0743
              else
                if j < 748 then
                  if j < 746 then
                    if j < 745 then
                      coefficients0744
                    else
                      coefficients0745
                  else
                    if j < 747 then
                      coefficients0746
                    else
                      coefficients0747
                else
                  if j < 750 then
                    if j < 749 then
                      coefficients0748
                    else
                      coefficients0749
                  else
                    if j < 751 then
                      coefficients0750
                    else
                      coefficients0751
            else
              if j < 760 then
                if j < 756 then
                  if j < 754 then
                    if j < 753 then
                      coefficients0752
                    else
                      coefficients0753
                  else
                    if j < 755 then
                      coefficients0754
                    else
                      coefficients0755
                else
                  if j < 758 then
                    if j < 757 then
                      coefficients0756
                    else
                      coefficients0757
                  else
                    if j < 759 then
                      coefficients0758
                    else
                      coefficients0759
              else
                if j < 764 then
                  if j < 762 then
                    if j < 761 then
                      coefficients0760
                    else
                      coefficients0761
                  else
                    if j < 763 then
                      coefficients0762
                    else
                      coefficients0763
                else
                  if j < 766 then
                    if j < 765 then
                      coefficients0764
                    else
                      coefficients0765
                  else
                    if j < 767 then
                      coefficients0766
                    else
                      coefficients0767
    else
      if j < 896 then
        if j < 832 then
          if j < 800 then
            if j < 784 then
              if j < 776 then
                if j < 772 then
                  if j < 770 then
                    if j < 769 then
                      coefficients0768
                    else
                      coefficients0769
                  else
                    if j < 771 then
                      coefficients0770
                    else
                      coefficients0771
                else
                  if j < 774 then
                    if j < 773 then
                      coefficients0772
                    else
                      coefficients0773
                  else
                    if j < 775 then
                      coefficients0774
                    else
                      coefficients0775
              else
                if j < 780 then
                  if j < 778 then
                    if j < 777 then
                      coefficients0776
                    else
                      coefficients0777
                  else
                    if j < 779 then
                      coefficients0778
                    else
                      coefficients0779
                else
                  if j < 782 then
                    if j < 781 then
                      coefficients0780
                    else
                      coefficients0781
                  else
                    if j < 783 then
                      coefficients0782
                    else
                      coefficients0783
            else
              if j < 792 then
                if j < 788 then
                  if j < 786 then
                    if j < 785 then
                      coefficients0784
                    else
                      coefficients0785
                  else
                    if j < 787 then
                      coefficients0786
                    else
                      coefficients0787
                else
                  if j < 790 then
                    if j < 789 then
                      coefficients0788
                    else
                      coefficients0789
                  else
                    if j < 791 then
                      coefficients0790
                    else
                      coefficients0791
              else
                if j < 796 then
                  if j < 794 then
                    if j < 793 then
                      coefficients0792
                    else
                      coefficients0793
                  else
                    if j < 795 then
                      coefficients0794
                    else
                      coefficients0795
                else
                  if j < 798 then
                    if j < 797 then
                      coefficients0796
                    else
                      coefficients0797
                  else
                    if j < 799 then
                      coefficients0798
                    else
                      coefficients0799
          else
            if j < 816 then
              if j < 808 then
                if j < 804 then
                  if j < 802 then
                    if j < 801 then
                      coefficients0800
                    else
                      coefficients0801
                  else
                    if j < 803 then
                      coefficients0802
                    else
                      coefficients0803
                else
                  if j < 806 then
                    if j < 805 then
                      coefficients0804
                    else
                      coefficients0805
                  else
                    if j < 807 then
                      coefficients0806
                    else
                      coefficients0807
              else
                if j < 812 then
                  if j < 810 then
                    if j < 809 then
                      coefficients0808
                    else
                      coefficients0809
                  else
                    if j < 811 then
                      coefficients0810
                    else
                      coefficients0811
                else
                  if j < 814 then
                    if j < 813 then
                      coefficients0812
                    else
                      coefficients0813
                  else
                    if j < 815 then
                      coefficients0814
                    else
                      coefficients0815
            else
              if j < 824 then
                if j < 820 then
                  if j < 818 then
                    if j < 817 then
                      coefficients0816
                    else
                      coefficients0817
                  else
                    if j < 819 then
                      coefficients0818
                    else
                      coefficients0819
                else
                  if j < 822 then
                    if j < 821 then
                      coefficients0820
                    else
                      coefficients0821
                  else
                    if j < 823 then
                      coefficients0822
                    else
                      coefficients0823
              else
                if j < 828 then
                  if j < 826 then
                    if j < 825 then
                      coefficients0824
                    else
                      coefficients0825
                  else
                    if j < 827 then
                      coefficients0826
                    else
                      coefficients0827
                else
                  if j < 830 then
                    if j < 829 then
                      coefficients0828
                    else
                      coefficients0829
                  else
                    if j < 831 then
                      coefficients0830
                    else
                      coefficients0831
        else
          if j < 864 then
            if j < 848 then
              if j < 840 then
                if j < 836 then
                  if j < 834 then
                    if j < 833 then
                      coefficients0832
                    else
                      coefficients0833
                  else
                    if j < 835 then
                      coefficients0834
                    else
                      coefficients0835
                else
                  if j < 838 then
                    if j < 837 then
                      coefficients0836
                    else
                      coefficients0837
                  else
                    if j < 839 then
                      coefficients0838
                    else
                      coefficients0839
              else
                if j < 844 then
                  if j < 842 then
                    if j < 841 then
                      coefficients0840
                    else
                      coefficients0841
                  else
                    if j < 843 then
                      coefficients0842
                    else
                      coefficients0843
                else
                  if j < 846 then
                    if j < 845 then
                      coefficients0844
                    else
                      coefficients0845
                  else
                    if j < 847 then
                      coefficients0846
                    else
                      coefficients0847
            else
              if j < 856 then
                if j < 852 then
                  if j < 850 then
                    if j < 849 then
                      coefficients0848
                    else
                      coefficients0849
                  else
                    if j < 851 then
                      coefficients0850
                    else
                      coefficients0851
                else
                  if j < 854 then
                    if j < 853 then
                      coefficients0852
                    else
                      coefficients0853
                  else
                    if j < 855 then
                      coefficients0854
                    else
                      coefficients0855
              else
                if j < 860 then
                  if j < 858 then
                    if j < 857 then
                      coefficients0856
                    else
                      coefficients0857
                  else
                    if j < 859 then
                      coefficients0858
                    else
                      coefficients0859
                else
                  if j < 862 then
                    if j < 861 then
                      coefficients0860
                    else
                      coefficients0861
                  else
                    if j < 863 then
                      coefficients0862
                    else
                      coefficients0863
          else
            if j < 880 then
              if j < 872 then
                if j < 868 then
                  if j < 866 then
                    if j < 865 then
                      coefficients0864
                    else
                      coefficients0865
                  else
                    if j < 867 then
                      coefficients0866
                    else
                      coefficients0867
                else
                  if j < 870 then
                    if j < 869 then
                      coefficients0868
                    else
                      coefficients0869
                  else
                    if j < 871 then
                      coefficients0870
                    else
                      coefficients0871
              else
                if j < 876 then
                  if j < 874 then
                    if j < 873 then
                      coefficients0872
                    else
                      coefficients0873
                  else
                    if j < 875 then
                      coefficients0874
                    else
                      coefficients0875
                else
                  if j < 878 then
                    if j < 877 then
                      coefficients0876
                    else
                      coefficients0877
                  else
                    if j < 879 then
                      coefficients0878
                    else
                      coefficients0879
            else
              if j < 888 then
                if j < 884 then
                  if j < 882 then
                    if j < 881 then
                      coefficients0880
                    else
                      coefficients0881
                  else
                    if j < 883 then
                      coefficients0882
                    else
                      coefficients0883
                else
                  if j < 886 then
                    if j < 885 then
                      coefficients0884
                    else
                      coefficients0885
                  else
                    if j < 887 then
                      coefficients0886
                    else
                      coefficients0887
              else
                if j < 892 then
                  if j < 890 then
                    if j < 889 then
                      coefficients0888
                    else
                      coefficients0889
                  else
                    if j < 891 then
                      coefficients0890
                    else
                      coefficients0891
                else
                  if j < 894 then
                    if j < 893 then
                      coefficients0892
                    else
                      coefficients0893
                  else
                    if j < 895 then
                      coefficients0894
                    else
                      coefficients0895
      else
        if j < 960 then
          if j < 928 then
            if j < 912 then
              if j < 904 then
                if j < 900 then
                  if j < 898 then
                    if j < 897 then
                      coefficients0896
                    else
                      coefficients0897
                  else
                    if j < 899 then
                      coefficients0898
                    else
                      coefficients0899
                else
                  if j < 902 then
                    if j < 901 then
                      coefficients0900
                    else
                      coefficients0901
                  else
                    if j < 903 then
                      coefficients0902
                    else
                      coefficients0903
              else
                if j < 908 then
                  if j < 906 then
                    if j < 905 then
                      coefficients0904
                    else
                      coefficients0905
                  else
                    if j < 907 then
                      coefficients0906
                    else
                      coefficients0907
                else
                  if j < 910 then
                    if j < 909 then
                      coefficients0908
                    else
                      coefficients0909
                  else
                    if j < 911 then
                      coefficients0910
                    else
                      coefficients0911
            else
              if j < 920 then
                if j < 916 then
                  if j < 914 then
                    if j < 913 then
                      coefficients0912
                    else
                      coefficients0913
                  else
                    if j < 915 then
                      coefficients0914
                    else
                      coefficients0915
                else
                  if j < 918 then
                    if j < 917 then
                      coefficients0916
                    else
                      coefficients0917
                  else
                    if j < 919 then
                      coefficients0918
                    else
                      coefficients0919
              else
                if j < 924 then
                  if j < 922 then
                    if j < 921 then
                      coefficients0920
                    else
                      coefficients0921
                  else
                    if j < 923 then
                      coefficients0922
                    else
                      coefficients0923
                else
                  if j < 926 then
                    if j < 925 then
                      coefficients0924
                    else
                      coefficients0925
                  else
                    if j < 927 then
                      coefficients0926
                    else
                      coefficients0927
          else
            if j < 944 then
              if j < 936 then
                if j < 932 then
                  if j < 930 then
                    if j < 929 then
                      coefficients0928
                    else
                      coefficients0929
                  else
                    if j < 931 then
                      coefficients0930
                    else
                      coefficients0931
                else
                  if j < 934 then
                    if j < 933 then
                      coefficients0932
                    else
                      coefficients0933
                  else
                    if j < 935 then
                      coefficients0934
                    else
                      coefficients0935
              else
                if j < 940 then
                  if j < 938 then
                    if j < 937 then
                      coefficients0936
                    else
                      coefficients0937
                  else
                    if j < 939 then
                      coefficients0938
                    else
                      coefficients0939
                else
                  if j < 942 then
                    if j < 941 then
                      coefficients0940
                    else
                      coefficients0941
                  else
                    if j < 943 then
                      coefficients0942
                    else
                      coefficients0943
            else
              if j < 952 then
                if j < 948 then
                  if j < 946 then
                    if j < 945 then
                      coefficients0944
                    else
                      coefficients0945
                  else
                    if j < 947 then
                      coefficients0946
                    else
                      coefficients0947
                else
                  if j < 950 then
                    if j < 949 then
                      coefficients0948
                    else
                      coefficients0949
                  else
                    if j < 951 then
                      coefficients0950
                    else
                      coefficients0951
              else
                if j < 956 then
                  if j < 954 then
                    if j < 953 then
                      coefficients0952
                    else
                      coefficients0953
                  else
                    if j < 955 then
                      coefficients0954
                    else
                      coefficients0955
                else
                  if j < 958 then
                    if j < 957 then
                      coefficients0956
                    else
                      coefficients0957
                  else
                    if j < 959 then
                      coefficients0958
                    else
                      coefficients0959
        else
          if j < 992 then
            if j < 976 then
              if j < 968 then
                if j < 964 then
                  if j < 962 then
                    if j < 961 then
                      coefficients0960
                    else
                      coefficients0961
                  else
                    if j < 963 then
                      coefficients0962
                    else
                      coefficients0963
                else
                  if j < 966 then
                    if j < 965 then
                      coefficients0964
                    else
                      coefficients0965
                  else
                    if j < 967 then
                      coefficients0966
                    else
                      coefficients0967
              else
                if j < 972 then
                  if j < 970 then
                    if j < 969 then
                      coefficients0968
                    else
                      coefficients0969
                  else
                    if j < 971 then
                      coefficients0970
                    else
                      coefficients0971
                else
                  if j < 974 then
                    if j < 973 then
                      coefficients0972
                    else
                      coefficients0973
                  else
                    if j < 975 then
                      coefficients0974
                    else
                      coefficients0975
            else
              if j < 984 then
                if j < 980 then
                  if j < 978 then
                    if j < 977 then
                      coefficients0976
                    else
                      coefficients0977
                  else
                    if j < 979 then
                      coefficients0978
                    else
                      coefficients0979
                else
                  if j < 982 then
                    if j < 981 then
                      coefficients0980
                    else
                      coefficients0981
                  else
                    if j < 983 then
                      coefficients0982
                    else
                      coefficients0983
              else
                if j < 988 then
                  if j < 986 then
                    if j < 985 then
                      coefficients0984
                    else
                      coefficients0985
                  else
                    if j < 987 then
                      coefficients0986
                    else
                      coefficients0987
                else
                  if j < 990 then
                    if j < 989 then
                      coefficients0988
                    else
                      coefficients0989
                  else
                    if j < 991 then
                      coefficients0990
                    else
                      coefficients0991
          else
            if j < 1008 then
              if j < 1000 then
                if j < 996 then
                  if j < 994 then
                    if j < 993 then
                      coefficients0992
                    else
                      coefficients0993
                  else
                    if j < 995 then
                      coefficients0994
                    else
                      coefficients0995
                else
                  if j < 998 then
                    if j < 997 then
                      coefficients0996
                    else
                      coefficients0997
                  else
                    if j < 999 then
                      coefficients0998
                    else
                      coefficients0999
              else
                if j < 1004 then
                  if j < 1002 then
                    if j < 1001 then
                      coefficients1000
                    else
                      coefficients1001
                  else
                    if j < 1003 then
                      coefficients1002
                    else
                      coefficients1003
                else
                  if j < 1006 then
                    if j < 1005 then
                      coefficients1004
                    else
                      coefficients1005
                  else
                    if j < 1007 then
                      coefficients1006
                    else
                      coefficients1007
            else
              if j < 1016 then
                if j < 1012 then
                  if j < 1010 then
                    if j < 1009 then
                      coefficients1008
                    else
                      coefficients1009
                  else
                    if j < 1011 then
                      coefficients1010
                    else
                      coefficients1011
                else
                  if j < 1014 then
                    if j < 1013 then
                      coefficients1012
                    else
                      coefficients1013
                  else
                    if j < 1015 then
                      coefficients1014
                    else
                      coefficients1015
              else
                if j < 1020 then
                  if j < 1018 then
                    if j < 1017 then
                      coefficients1016
                    else
                      coefficients1017
                  else
                    if j < 1019 then
                      coefficients1018
                    else
                      coefficients1019
                else
                  if j < 1022 then
                    if j < 1021 then
                      coefficients1020
                    else
                      coefficients1021
                  else
                    if j < 1023 then
                      coefficients1022
                    else
                      coefficients1023

end
end ErdosOverlap.Native6Grid
