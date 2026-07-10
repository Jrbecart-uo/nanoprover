-- AUTO-GENERATED Collatz theorem database (see collatz_discover.py)
def step (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1
def iter : Nat → Nat → Nat
  | 0,     n => n
  | k + 1, n => iter k (step n)
def reaches1 (n : Nat) : Prop := ∃ k, iter k n = 1

theorem step_double (n : Nat) : step (2 * n) = n := by
  unfold step
  rw [if_pos (Nat.mul_mod_right 2 n), Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

theorem reaches1_double {n : Nat} : reaches1 n → reaches1 (2 * n) := by
  intro ⟨k, hk⟩
  exact ⟨k + 1, by show iter k (step (2 * n)) = 1; rw [step_double]; exact hk⟩

theorem reaches1_odd {n : Nat} (hodd : n % 2 = 1) :
    reaches1 (3 * n + 1) → reaches1 n := by
  intro ⟨k, hk⟩
  refine ⟨k + 1, ?_⟩
  show iter k (step n) = 1
  unfold step
  rw [if_neg (by omega : ¬ n % 2 = 0)]
  exact hk

theorem c_1 : reaches1 1 := ⟨0, rfl⟩

-- ===== discovered theorems (400) =====
theorem c_2 : reaches1 2 := reaches1_double c_1
theorem c_4 : reaches1 4 := reaches1_double c_2
theorem c_8 : reaches1 8 := reaches1_double c_4
theorem c_16 : reaches1 16 := reaches1_double c_8
theorem c_32 : reaches1 32 := reaches1_double c_16
theorem c_5 : reaches1 5 := reaches1_odd (n := 5) (by decide) c_16
theorem c_64 : reaches1 64 := reaches1_double c_32
theorem c_10 : reaches1 10 := reaches1_double c_5
theorem c_128 : reaches1 128 := reaches1_double c_64
theorem c_21 : reaches1 21 := reaches1_odd (n := 21) (by decide) c_64
theorem c_20 : reaches1 20 := reaches1_double c_10
theorem c_3 : reaches1 3 := reaches1_odd (n := 3) (by decide) c_10
theorem c_256 : reaches1 256 := reaches1_double c_128
theorem c_42 : reaches1 42 := reaches1_double c_21
theorem c_40 : reaches1 40 := reaches1_double c_20
theorem c_6 : reaches1 6 := reaches1_double c_3
theorem c_512 : reaches1 512 := reaches1_double c_256
theorem c_85 : reaches1 85 := reaches1_odd (n := 85) (by decide) c_256
theorem c_84 : reaches1 84 := reaches1_double c_42
theorem c_80 : reaches1 80 := reaches1_double c_40
theorem c_13 : reaches1 13 := reaches1_odd (n := 13) (by decide) c_40
theorem c_12 : reaches1 12 := reaches1_double c_6
theorem c_1024 : reaches1 1024 := reaches1_double c_512
theorem c_170 : reaches1 170 := reaches1_double c_85
theorem c_168 : reaches1 168 := reaches1_double c_84
theorem c_160 : reaches1 160 := reaches1_double c_80
theorem c_26 : reaches1 26 := reaches1_double c_13
theorem c_24 : reaches1 24 := reaches1_double c_12
theorem c_2048 : reaches1 2048 := reaches1_double c_1024
theorem c_341 : reaches1 341 := reaches1_odd (n := 341) (by decide) c_1024
theorem c_340 : reaches1 340 := reaches1_double c_170
theorem c_336 : reaches1 336 := reaches1_double c_168
theorem c_320 : reaches1 320 := reaches1_double c_160
theorem c_53 : reaches1 53 := reaches1_odd (n := 53) (by decide) c_160
theorem c_52 : reaches1 52 := reaches1_double c_26
theorem c_48 : reaches1 48 := reaches1_double c_24
theorem c_4096 : reaches1 4096 := reaches1_double c_2048
theorem c_682 : reaches1 682 := reaches1_double c_341
theorem c_680 : reaches1 680 := reaches1_double c_340
theorem c_113 : reaches1 113 := reaches1_odd (n := 113) (by decide) c_340
theorem c_672 : reaches1 672 := reaches1_double c_336
theorem c_640 : reaches1 640 := reaches1_double c_320
theorem c_106 : reaches1 106 := reaches1_double c_53
theorem c_104 : reaches1 104 := reaches1_double c_52
theorem c_17 : reaches1 17 := reaches1_odd (n := 17) (by decide) c_52
theorem c_96 : reaches1 96 := reaches1_double c_48
theorem c_8192 : reaches1 8192 := reaches1_double c_4096
theorem c_1365 : reaches1 1365 := reaches1_odd (n := 1365) (by decide) c_4096
theorem c_1364 : reaches1 1364 := reaches1_double c_682
theorem c_227 : reaches1 227 := reaches1_odd (n := 227) (by decide) c_682
theorem c_1360 : reaches1 1360 := reaches1_double c_680
theorem c_226 : reaches1 226 := reaches1_double c_113
theorem c_1344 : reaches1 1344 := reaches1_double c_672
theorem c_1280 : reaches1 1280 := reaches1_double c_640
theorem c_213 : reaches1 213 := reaches1_odd (n := 213) (by decide) c_640
theorem c_212 : reaches1 212 := reaches1_double c_106
theorem c_35 : reaches1 35 := reaches1_odd (n := 35) (by decide) c_106
theorem c_208 : reaches1 208 := reaches1_double c_104
theorem c_34 : reaches1 34 := reaches1_double c_17
theorem c_192 : reaches1 192 := reaches1_double c_96
theorem c_16384 : reaches1 16384 := reaches1_double c_8192
theorem c_2730 : reaches1 2730 := reaches1_double c_1365
theorem c_2728 : reaches1 2728 := reaches1_double c_1364
theorem c_454 : reaches1 454 := reaches1_double c_227
theorem c_2720 : reaches1 2720 := reaches1_double c_1360
theorem c_453 : reaches1 453 := reaches1_odd (n := 453) (by decide) c_1360
theorem c_452 : reaches1 452 := reaches1_double c_226
theorem c_75 : reaches1 75 := reaches1_odd (n := 75) (by decide) c_226
theorem c_2688 : reaches1 2688 := reaches1_double c_1344
theorem c_2560 : reaches1 2560 := reaches1_double c_1280
theorem c_426 : reaches1 426 := reaches1_double c_213
theorem c_424 : reaches1 424 := reaches1_double c_212
theorem c_70 : reaches1 70 := reaches1_double c_35
theorem c_416 : reaches1 416 := reaches1_double c_208
theorem c_69 : reaches1 69 := reaches1_odd (n := 69) (by decide) c_208
theorem c_68 : reaches1 68 := reaches1_double c_34
theorem c_11 : reaches1 11 := reaches1_odd (n := 11) (by decide) c_34
theorem c_384 : reaches1 384 := reaches1_double c_192
theorem c_32768 : reaches1 32768 := reaches1_double c_16384
theorem c_5461 : reaches1 5461 := reaches1_odd (n := 5461) (by decide) c_16384
theorem c_5460 : reaches1 5460 := reaches1_double c_2730
theorem c_5456 : reaches1 5456 := reaches1_double c_2728
theorem c_909 : reaches1 909 := reaches1_odd (n := 909) (by decide) c_2728
theorem c_908 : reaches1 908 := reaches1_double c_454
theorem c_151 : reaches1 151 := reaches1_odd (n := 151) (by decide) c_454
theorem c_5440 : reaches1 5440 := reaches1_double c_2720
theorem c_906 : reaches1 906 := reaches1_double c_453
theorem c_904 : reaches1 904 := reaches1_double c_452
theorem c_150 : reaches1 150 := reaches1_double c_75
theorem c_5376 : reaches1 5376 := reaches1_double c_2688
theorem c_5120 : reaches1 5120 := reaches1_double c_2560
theorem c_853 : reaches1 853 := reaches1_odd (n := 853) (by decide) c_2560
theorem c_852 : reaches1 852 := reaches1_double c_426
theorem c_848 : reaches1 848 := reaches1_double c_424
theorem c_141 : reaches1 141 := reaches1_odd (n := 141) (by decide) c_424
theorem c_140 : reaches1 140 := reaches1_double c_70
theorem c_23 : reaches1 23 := reaches1_odd (n := 23) (by decide) c_70
theorem c_832 : reaches1 832 := reaches1_double c_416
theorem c_138 : reaches1 138 := reaches1_double c_69
theorem c_136 : reaches1 136 := reaches1_double c_68
theorem c_22 : reaches1 22 := reaches1_double c_11
theorem c_768 : reaches1 768 := reaches1_double c_384
theorem c_65536 : reaches1 65536 := reaches1_double c_32768
theorem c_10922 : reaches1 10922 := reaches1_double c_5461
theorem c_10920 : reaches1 10920 := reaches1_double c_5460
theorem c_10912 : reaches1 10912 := reaches1_double c_5456
theorem c_1818 : reaches1 1818 := reaches1_double c_909
theorem c_1816 : reaches1 1816 := reaches1_double c_908
theorem c_302 : reaches1 302 := reaches1_double c_151
theorem c_10880 : reaches1 10880 := reaches1_double c_5440
theorem c_1813 : reaches1 1813 := reaches1_odd (n := 1813) (by decide) c_5440
theorem c_1812 : reaches1 1812 := reaches1_double c_906
theorem c_1808 : reaches1 1808 := reaches1_double c_904
theorem c_301 : reaches1 301 := reaches1_odd (n := 301) (by decide) c_904
theorem c_300 : reaches1 300 := reaches1_double c_150
theorem c_10752 : reaches1 10752 := reaches1_double c_5376
theorem c_10240 : reaches1 10240 := reaches1_double c_5120
theorem c_1706 : reaches1 1706 := reaches1_double c_853
theorem c_1704 : reaches1 1704 := reaches1_double c_852
theorem c_1696 : reaches1 1696 := reaches1_double c_848
theorem c_282 : reaches1 282 := reaches1_double c_141
theorem c_280 : reaches1 280 := reaches1_double c_140
theorem c_46 : reaches1 46 := reaches1_double c_23
theorem c_1664 : reaches1 1664 := reaches1_double c_832
theorem c_277 : reaches1 277 := reaches1_odd (n := 277) (by decide) c_832
theorem c_276 : reaches1 276 := reaches1_double c_138
theorem c_272 : reaches1 272 := reaches1_double c_136
theorem c_45 : reaches1 45 := reaches1_odd (n := 45) (by decide) c_136
theorem c_44 : reaches1 44 := reaches1_double c_22
theorem c_7 : reaches1 7 := reaches1_odd (n := 7) (by decide) c_22
theorem c_1536 : reaches1 1536 := reaches1_double c_768
theorem c_131072 : reaches1 131072 := reaches1_double c_65536
theorem c_21845 : reaches1 21845 := reaches1_odd (n := 21845) (by decide) c_65536
theorem c_21844 : reaches1 21844 := reaches1_double c_10922
theorem c_21840 : reaches1 21840 := reaches1_double c_10920
theorem c_21824 : reaches1 21824 := reaches1_double c_10912
theorem c_3637 : reaches1 3637 := reaches1_odd (n := 3637) (by decide) c_10912
theorem c_3636 : reaches1 3636 := reaches1_double c_1818
theorem c_3632 : reaches1 3632 := reaches1_double c_1816
theorem c_605 : reaches1 605 := reaches1_odd (n := 605) (by decide) c_1816
theorem c_604 : reaches1 604 := reaches1_double c_302
theorem c_21760 : reaches1 21760 := reaches1_double c_10880
theorem c_3626 : reaches1 3626 := reaches1_double c_1813
theorem c_3624 : reaches1 3624 := reaches1_double c_1812
theorem c_3616 : reaches1 3616 := reaches1_double c_1808
theorem c_602 : reaches1 602 := reaches1_double c_301
theorem c_600 : reaches1 600 := reaches1_double c_300
theorem c_21504 : reaches1 21504 := reaches1_double c_10752
theorem c_20480 : reaches1 20480 := reaches1_double c_10240
theorem c_3413 : reaches1 3413 := reaches1_odd (n := 3413) (by decide) c_10240
theorem c_3412 : reaches1 3412 := reaches1_double c_1706
theorem c_3408 : reaches1 3408 := reaches1_double c_1704
theorem c_3392 : reaches1 3392 := reaches1_double c_1696
theorem c_565 : reaches1 565 := reaches1_odd (n := 565) (by decide) c_1696
theorem c_564 : reaches1 564 := reaches1_double c_282
theorem c_560 : reaches1 560 := reaches1_double c_280
theorem c_93 : reaches1 93 := reaches1_odd (n := 93) (by decide) c_280
theorem c_92 : reaches1 92 := reaches1_double c_46
theorem c_15 : reaches1 15 := reaches1_odd (n := 15) (by decide) c_46
theorem c_3328 : reaches1 3328 := reaches1_double c_1664
theorem c_554 : reaches1 554 := reaches1_double c_277
theorem c_552 : reaches1 552 := reaches1_double c_276
theorem c_544 : reaches1 544 := reaches1_double c_272
theorem c_90 : reaches1 90 := reaches1_double c_45
theorem c_88 : reaches1 88 := reaches1_double c_44
theorem c_14 : reaches1 14 := reaches1_double c_7
theorem c_3072 : reaches1 3072 := reaches1_double c_1536
theorem c_43690 : reaches1 43690 := reaches1_double c_21845
theorem c_43688 : reaches1 43688 := reaches1_double c_21844
theorem c_7281 : reaches1 7281 := reaches1_odd (n := 7281) (by decide) c_21844
theorem c_43680 : reaches1 43680 := reaches1_double c_21840
theorem c_43648 : reaches1 43648 := reaches1_double c_21824
theorem c_7274 : reaches1 7274 := reaches1_double c_3637
theorem c_7272 : reaches1 7272 := reaches1_double c_3636
theorem c_7264 : reaches1 7264 := reaches1_double c_3632
theorem c_1210 : reaches1 1210 := reaches1_double c_605
theorem c_1208 : reaches1 1208 := reaches1_double c_604
theorem c_201 : reaches1 201 := reaches1_odd (n := 201) (by decide) c_604
theorem c_43520 : reaches1 43520 := reaches1_double c_21760
theorem c_7253 : reaches1 7253 := reaches1_odd (n := 7253) (by decide) c_21760
theorem c_7252 : reaches1 7252 := reaches1_double c_3626
theorem c_7248 : reaches1 7248 := reaches1_double c_3624
theorem c_7232 : reaches1 7232 := reaches1_double c_3616
theorem c_1205 : reaches1 1205 := reaches1_odd (n := 1205) (by decide) c_3616
theorem c_1204 : reaches1 1204 := reaches1_double c_602
theorem c_1200 : reaches1 1200 := reaches1_double c_600
theorem c_43008 : reaches1 43008 := reaches1_double c_21504
theorem c_40960 : reaches1 40960 := reaches1_double c_20480
theorem c_6826 : reaches1 6826 := reaches1_double c_3413
theorem c_6824 : reaches1 6824 := reaches1_double c_3412
theorem c_1137 : reaches1 1137 := reaches1_odd (n := 1137) (by decide) c_3412
theorem c_6816 : reaches1 6816 := reaches1_double c_3408
theorem c_6784 : reaches1 6784 := reaches1_double c_3392
theorem c_1130 : reaches1 1130 := reaches1_double c_565
theorem c_1128 : reaches1 1128 := reaches1_double c_564
theorem c_1120 : reaches1 1120 := reaches1_double c_560
theorem c_186 : reaches1 186 := reaches1_double c_93
theorem c_184 : reaches1 184 := reaches1_double c_92
theorem c_30 : reaches1 30 := reaches1_double c_15
theorem c_6656 : reaches1 6656 := reaches1_double c_3328
theorem c_1109 : reaches1 1109 := reaches1_odd (n := 1109) (by decide) c_3328
theorem c_1108 : reaches1 1108 := reaches1_double c_554
theorem c_1104 : reaches1 1104 := reaches1_double c_552
theorem c_1088 : reaches1 1088 := reaches1_double c_544
theorem c_181 : reaches1 181 := reaches1_odd (n := 181) (by decide) c_544
theorem c_180 : reaches1 180 := reaches1_double c_90
theorem c_176 : reaches1 176 := reaches1_double c_88
theorem c_29 : reaches1 29 := reaches1_odd (n := 29) (by decide) c_88
theorem c_28 : reaches1 28 := reaches1_double c_14
theorem c_6144 : reaches1 6144 := reaches1_double c_3072
theorem c_87380 : reaches1 87380 := reaches1_double c_43690
theorem c_14563 : reaches1 14563 := reaches1_odd (n := 14563) (by decide) c_43690
theorem c_87376 : reaches1 87376 := reaches1_double c_43688
theorem c_14562 : reaches1 14562 := reaches1_double c_7281
theorem c_87360 : reaches1 87360 := reaches1_double c_43680
theorem c_87296 : reaches1 87296 := reaches1_double c_43648
theorem c_14549 : reaches1 14549 := reaches1_odd (n := 14549) (by decide) c_43648
theorem c_14548 : reaches1 14548 := reaches1_double c_7274
theorem c_14544 : reaches1 14544 := reaches1_double c_7272
theorem c_14528 : reaches1 14528 := reaches1_double c_7264
theorem c_2421 : reaches1 2421 := reaches1_odd (n := 2421) (by decide) c_7264
theorem c_2420 : reaches1 2420 := reaches1_double c_1210
theorem c_403 : reaches1 403 := reaches1_odd (n := 403) (by decide) c_1210
theorem c_2416 : reaches1 2416 := reaches1_double c_1208
theorem c_402 : reaches1 402 := reaches1_double c_201
theorem c_87040 : reaches1 87040 := reaches1_double c_43520
theorem c_14506 : reaches1 14506 := reaches1_double c_7253
theorem c_14504 : reaches1 14504 := reaches1_double c_7252
theorem c_2417 : reaches1 2417 := reaches1_odd (n := 2417) (by decide) c_7252
theorem c_14496 : reaches1 14496 := reaches1_double c_7248
theorem c_14464 : reaches1 14464 := reaches1_double c_7232
theorem c_2410 : reaches1 2410 := reaches1_double c_1205
theorem c_2408 : reaches1 2408 := reaches1_double c_1204
theorem c_401 : reaches1 401 := reaches1_odd (n := 401) (by decide) c_1204
theorem c_2400 : reaches1 2400 := reaches1_double c_1200
theorem c_86016 : reaches1 86016 := reaches1_double c_43008
theorem c_81920 : reaches1 81920 := reaches1_double c_40960
theorem c_13653 : reaches1 13653 := reaches1_odd (n := 13653) (by decide) c_40960
theorem c_13652 : reaches1 13652 := reaches1_double c_6826
theorem c_2275 : reaches1 2275 := reaches1_odd (n := 2275) (by decide) c_6826
theorem c_13648 : reaches1 13648 := reaches1_double c_6824
theorem c_2274 : reaches1 2274 := reaches1_double c_1137
theorem c_13632 : reaches1 13632 := reaches1_double c_6816
theorem c_13568 : reaches1 13568 := reaches1_double c_6784
theorem c_2261 : reaches1 2261 := reaches1_odd (n := 2261) (by decide) c_6784
theorem c_2260 : reaches1 2260 := reaches1_double c_1130
theorem c_2256 : reaches1 2256 := reaches1_double c_1128
theorem c_2240 : reaches1 2240 := reaches1_double c_1120
theorem c_373 : reaches1 373 := reaches1_odd (n := 373) (by decide) c_1120
theorem c_372 : reaches1 372 := reaches1_double c_186
theorem c_368 : reaches1 368 := reaches1_double c_184
theorem c_61 : reaches1 61 := reaches1_odd (n := 61) (by decide) c_184
theorem c_60 : reaches1 60 := reaches1_double c_30
theorem c_13312 : reaches1 13312 := reaches1_double c_6656
theorem c_2218 : reaches1 2218 := reaches1_double c_1109
theorem c_2216 : reaches1 2216 := reaches1_double c_1108
theorem c_369 : reaches1 369 := reaches1_odd (n := 369) (by decide) c_1108
theorem c_2208 : reaches1 2208 := reaches1_double c_1104
theorem c_2176 : reaches1 2176 := reaches1_double c_1088
theorem c_362 : reaches1 362 := reaches1_double c_181
theorem c_360 : reaches1 360 := reaches1_double c_180
theorem c_352 : reaches1 352 := reaches1_double c_176
theorem c_58 : reaches1 58 := reaches1_double c_29
theorem c_56 : reaches1 56 := reaches1_double c_28
theorem c_9 : reaches1 9 := reaches1_odd (n := 9) (by decide) c_28
theorem c_12288 : reaches1 12288 := reaches1_double c_6144
theorem c_174760 : reaches1 174760 := reaches1_double c_87380
theorem c_29126 : reaches1 29126 := reaches1_double c_14563
theorem c_174752 : reaches1 174752 := reaches1_double c_87376
theorem c_29125 : reaches1 29125 := reaches1_odd (n := 29125) (by decide) c_87376
theorem c_29124 : reaches1 29124 := reaches1_double c_14562
theorem c_174720 : reaches1 174720 := reaches1_double c_87360
theorem c_174592 : reaches1 174592 := reaches1_double c_87296
theorem c_29098 : reaches1 29098 := reaches1_double c_14549
theorem c_29096 : reaches1 29096 := reaches1_double c_14548
theorem c_4849 : reaches1 4849 := reaches1_odd (n := 4849) (by decide) c_14548
theorem c_29088 : reaches1 29088 := reaches1_double c_14544
theorem c_29056 : reaches1 29056 := reaches1_double c_14528
theorem c_4842 : reaches1 4842 := reaches1_double c_2421
theorem c_4840 : reaches1 4840 := reaches1_double c_2420
theorem c_806 : reaches1 806 := reaches1_double c_403
theorem c_4832 : reaches1 4832 := reaches1_double c_2416
theorem c_805 : reaches1 805 := reaches1_odd (n := 805) (by decide) c_2416
theorem c_804 : reaches1 804 := reaches1_double c_402
theorem c_174080 : reaches1 174080 := reaches1_double c_87040
theorem c_29013 : reaches1 29013 := reaches1_odd (n := 29013) (by decide) c_87040
theorem c_29012 : reaches1 29012 := reaches1_double c_14506
theorem c_4835 : reaches1 4835 := reaches1_odd (n := 4835) (by decide) c_14506
theorem c_29008 : reaches1 29008 := reaches1_double c_14504
theorem c_4834 : reaches1 4834 := reaches1_double c_2417
theorem c_28992 : reaches1 28992 := reaches1_double c_14496
theorem c_28928 : reaches1 28928 := reaches1_double c_14464
theorem c_4821 : reaches1 4821 := reaches1_odd (n := 4821) (by decide) c_14464
theorem c_4820 : reaches1 4820 := reaches1_double c_2410
theorem c_803 : reaches1 803 := reaches1_odd (n := 803) (by decide) c_2410
theorem c_4816 : reaches1 4816 := reaches1_double c_2408
theorem c_802 : reaches1 802 := reaches1_double c_401
theorem c_4800 : reaches1 4800 := reaches1_double c_2400
theorem c_172032 : reaches1 172032 := reaches1_double c_86016
theorem c_163840 : reaches1 163840 := reaches1_double c_81920
theorem c_27306 : reaches1 27306 := reaches1_double c_13653
theorem c_27304 : reaches1 27304 := reaches1_double c_13652
theorem c_4550 : reaches1 4550 := reaches1_double c_2275
theorem c_27296 : reaches1 27296 := reaches1_double c_13648
theorem c_4549 : reaches1 4549 := reaches1_odd (n := 4549) (by decide) c_13648
theorem c_4548 : reaches1 4548 := reaches1_double c_2274
theorem c_27264 : reaches1 27264 := reaches1_double c_13632
theorem c_27136 : reaches1 27136 := reaches1_double c_13568
theorem c_4522 : reaches1 4522 := reaches1_double c_2261
theorem c_4520 : reaches1 4520 := reaches1_double c_2260
theorem c_753 : reaches1 753 := reaches1_odd (n := 753) (by decide) c_2260
theorem c_4512 : reaches1 4512 := reaches1_double c_2256
theorem c_4480 : reaches1 4480 := reaches1_double c_2240
theorem c_746 : reaches1 746 := reaches1_double c_373
theorem c_744 : reaches1 744 := reaches1_double c_372
theorem c_736 : reaches1 736 := reaches1_double c_368
theorem c_122 : reaches1 122 := reaches1_double c_61
theorem c_120 : reaches1 120 := reaches1_double c_60
theorem c_26624 : reaches1 26624 := reaches1_double c_13312
theorem c_4437 : reaches1 4437 := reaches1_odd (n := 4437) (by decide) c_13312
theorem c_4436 : reaches1 4436 := reaches1_double c_2218
theorem c_739 : reaches1 739 := reaches1_odd (n := 739) (by decide) c_2218
theorem c_4432 : reaches1 4432 := reaches1_double c_2216
theorem c_738 : reaches1 738 := reaches1_double c_369
theorem c_4416 : reaches1 4416 := reaches1_double c_2208
theorem c_4352 : reaches1 4352 := reaches1_double c_2176
theorem c_725 : reaches1 725 := reaches1_odd (n := 725) (by decide) c_2176
theorem c_724 : reaches1 724 := reaches1_double c_362
theorem c_720 : reaches1 720 := reaches1_double c_360
theorem c_704 : reaches1 704 := reaches1_double c_352
theorem c_117 : reaches1 117 := reaches1_odd (n := 117) (by decide) c_352
theorem c_116 : reaches1 116 := reaches1_double c_58
theorem c_19 : reaches1 19 := reaches1_odd (n := 19) (by decide) c_58
theorem c_112 : reaches1 112 := reaches1_double c_56
theorem c_18 : reaches1 18 := reaches1_double c_9
theorem c_24576 : reaches1 24576 := reaches1_double c_12288
theorem c_58253 : reaches1 58253 := reaches1_odd (n := 58253) (by decide) c_174760
theorem c_58252 : reaches1 58252 := reaches1_double c_29126
theorem c_58250 : reaches1 58250 := reaches1_double c_29125
theorem c_58248 : reaches1 58248 := reaches1_double c_29124
theorem c_58197 : reaches1 58197 := reaches1_odd (n := 58197) (by decide) c_174592
theorem c_58196 : reaches1 58196 := reaches1_double c_29098
theorem c_9699 : reaches1 9699 := reaches1_odd (n := 9699) (by decide) c_29098
theorem c_58192 : reaches1 58192 := reaches1_double c_29096
theorem c_9698 : reaches1 9698 := reaches1_double c_4849
theorem c_58176 : reaches1 58176 := reaches1_double c_29088
theorem c_58112 : reaches1 58112 := reaches1_double c_29056
theorem c_9685 : reaches1 9685 := reaches1_odd (n := 9685) (by decide) c_29056
theorem c_9684 : reaches1 9684 := reaches1_double c_4842
theorem c_9680 : reaches1 9680 := reaches1_double c_4840
theorem c_1613 : reaches1 1613 := reaches1_odd (n := 1613) (by decide) c_4840
theorem c_1612 : reaches1 1612 := reaches1_double c_806
theorem c_9664 : reaches1 9664 := reaches1_double c_4832
theorem c_1610 : reaches1 1610 := reaches1_double c_805
theorem c_1608 : reaches1 1608 := reaches1_double c_804
theorem c_58026 : reaches1 58026 := reaches1_double c_29013
theorem c_58024 : reaches1 58024 := reaches1_double c_29012
theorem c_9670 : reaches1 9670 := reaches1_double c_4835
theorem c_58016 : reaches1 58016 := reaches1_double c_29008
theorem c_9669 : reaches1 9669 := reaches1_odd (n := 9669) (by decide) c_29008
theorem c_9668 : reaches1 9668 := reaches1_double c_4834
theorem c_1611 : reaches1 1611 := reaches1_odd (n := 1611) (by decide) c_4834
theorem c_57984 : reaches1 57984 := reaches1_double c_28992
theorem c_57856 : reaches1 57856 := reaches1_double c_28928
theorem c_9642 : reaches1 9642 := reaches1_double c_4821
theorem c_9640 : reaches1 9640 := reaches1_double c_4820
theorem c_1606 : reaches1 1606 := reaches1_double c_803
theorem c_9632 : reaches1 9632 := reaches1_double c_4816
theorem c_1605 : reaches1 1605 := reaches1_odd (n := 1605) (by decide) c_4816
theorem c_1604 : reaches1 1604 := reaches1_double c_802
theorem c_267 : reaches1 267 := reaches1_odd (n := 267) (by decide) c_802
theorem c_9600 : reaches1 9600 := reaches1_double c_4800
theorem c_54613 : reaches1 54613 := reaches1_odd (n := 54613) (by decide) c_163840
theorem c_54612 : reaches1 54612 := reaches1_double c_27306
theorem c_54608 : reaches1 54608 := reaches1_double c_27304
theorem c_9101 : reaches1 9101 := reaches1_odd (n := 9101) (by decide) c_27304
theorem c_9100 : reaches1 9100 := reaches1_double c_4550
theorem c_54592 : reaches1 54592 := reaches1_double c_27296
theorem c_9098 : reaches1 9098 := reaches1_double c_4549
theorem c_9096 : reaches1 9096 := reaches1_double c_4548
theorem c_54528 : reaches1 54528 := reaches1_double c_27264
theorem c_54272 : reaches1 54272 := reaches1_double c_27136
theorem c_9045 : reaches1 9045 := reaches1_odd (n := 9045) (by decide) c_27136
theorem c_9044 : reaches1 9044 := reaches1_double c_4522
theorem c_1507 : reaches1 1507 := reaches1_odd (n := 1507) (by decide) c_4522
theorem c_9040 : reaches1 9040 := reaches1_double c_4520
theorem c_1506 : reaches1 1506 := reaches1_double c_753
theorem c_9024 : reaches1 9024 := reaches1_double c_4512
theorem c_8960 : reaches1 8960 := reaches1_double c_4480
theorem c_1493 : reaches1 1493 := reaches1_odd (n := 1493) (by decide) c_4480
theorem c_1492 : reaches1 1492 := reaches1_double c_746
theorem c_1488 : reaches1 1488 := reaches1_double c_744
theorem c_1472 : reaches1 1472 := reaches1_double c_736
theorem c_245 : reaches1 245 := reaches1_odd (n := 245) (by decide) c_736
theorem c_244 : reaches1 244 := reaches1_double c_122
theorem c_240 : reaches1 240 := reaches1_double c_120
theorem c_53248 : reaches1 53248 := reaches1_double c_26624
theorem c_8874 : reaches1 8874 := reaches1_double c_4437
theorem c_8872 : reaches1 8872 := reaches1_double c_4436
theorem c_1478 : reaches1 1478 := reaches1_double c_739
