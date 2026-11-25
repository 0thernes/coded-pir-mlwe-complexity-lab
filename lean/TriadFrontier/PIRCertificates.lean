module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

/-!
# Certified Finite-Field & Polymatroid Witnesses (`CS-053`)

100% zero-Mathlib kernel-checked certificates (ZERO `native_decide`, ZERO `sorry`),
using balanced O(log N) binary-tree lookups so every independent Lean 4.35 kernel
(`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`)
verifies all certificates in milliseconds without increasing `maxRecDepth`.
-/

namespace TriadFrontier.PIRCertificates

@[expose] public section

def allBelow (n : Nat) (p : Nat → Bool) : Bool :=
  match n with
  | 0 => true
  | k + 1 => allBelow k p && p k

def sumMod11 (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => (sumMod11 k f + f k) % 11

-- ============================================================================
-- Part 1: F_11 Byzantine Rate-2/5 Zero-Error PIR Certificate (N=6, K=2, T=2, B=1)
-- ============================================================================

def f11VRow (idx : Nat) : Nat :=
  (if idx < 9 then (if idx < 4 then (if idx < 2 then (if idx < 1 then 696321 else 10489872) else (if idx < 3 then 1114368 else 225281)) else (if idx < 6 then (if idx < 5 then 3153936 else 4325632) else (if idx < 7 then 401409 else (if idx < 8 then 6303760 else 9634048)))) else (if idx < 13 then (if idx < 11 then (if idx < 10 then 155649 else 2113552) else (if idx < 12 then 5505280 else 491521)) else (if idx < 15 then (if idx < 14 then 7360528 else 3473664) else (if idx < 16 then 294913 else (if idx < 17 then 4218896 else 3539200)))))

def f11V (k r c : Nat) : Nat :=
  (f11VRow (k * 3 + r) >>> (4 * c)) &&& 15

def f11URow (idx : Nat) : Nat :=
  (if idx < 9 then (if idx < 4 then (if idx < 2 then (if idx < 1 then 1 else 272) else (if idx < 3 then 69632 else 1)) else (if idx < 6 then (if idx < 5 then 528 else 135168) else (if idx < 7 then 1 else (if idx < 8 then 784 else 200704)))) else (if idx < 13 then (if idx < 11 then (if idx < 10 then 1 else 1040) else (if idx < 12 then 266240 else 1)) else (if idx < 15 then (if idx < 14 then 1296 else 331776) else (if idx < 16 then 1 else (if idx < 17 then 1552 else 397312)))))

def f11U (k r c : Nat) : Nat :=
  (f11URow (k * 3 + r) >>> (4 * c)) &&& 15

def f11ASelRow (idx : Nat) : Nat :=
  (if idx < 6 then (if idx < 3 then (if idx < 1 then 2724 else (if idx < 2 then 2595 else 275)) else (if idx < 4 then 2690 else (if idx < 5 then 2454 else 1539))) else (if idx < 9 then (if idx < 7 then 1699 else (if idx < 8 then 1925 else 311)) else (if idx < 10 then 2577 else (if idx < 11 then 1322 else 1684))))

def f11ASel (k r c : Nat) : Nat :=
  (f11ASelRow (k * 2 + r) >>> (4 * c)) &&& 15

def f11BSelRow (idx : Nat) : Nat :=
  (if idx < 6 then (if idx < 3 then (if idx < 1 then 1930 else (if idx < 2 then 516 else 370)) else (if idx < 4 then 1946 else (if idx < 5 then 519 else 803))) else (if idx < 9 then (if idx < 7 then 163 else (if idx < 8 then 1914 else 1190)) else (if idx < 10 then 1541 else (if idx < 11 then 421 else 18))))

def f11BSel (k r c : Nat) : Nat :=
  (f11BSelRow (k * 2 + r) >>> (4 * c)) &&& 15

def f11DesInvRow (idx : Nat) : Nat :=
  (if idx < 90 then (if idx < 45 then (if idx < 22 then (if idx < 11 then (if idx < 5 then (if idx < 2 then (if idx < 1 then 113950122988612 else 134145798112320) else (if idx < 3 then 175939045557248 else (if idx < 4 then 92464776038260 else 21524063606050))) else (if idx < 8 then (if idx < 6 then 45103068809504 else (if idx < 7 then 71479066839715 else 131530572919671)) else (if idx < 9 then 184860847204761 else (if idx < 10 then 134147140420720 else 142955035101584)))) else (if idx < 16 then (if idx < 13 then (if idx < 12 then 35205853219072 else 43457152377105) else (if idx < 14 then 131952134193424 else (if idx < 15 then 140771854385408 else 162957931199143))) else (if idx < 19 then (if idx < 17 then 74052008114807 else (if idx < 18 then 5498363904112 else 73672719221283)) else (if idx < 20 then 96251865826116 else (if idx < 21 then 132380158870596 else 131950523711808))))) else (if idx < 33 then (if idx < 27 then (if idx < 24 then (if idx < 23 then 147345304192064 else 105587480200192) else (if idx < 25 then 59474060646536 else (if idx < 26 then 106678936733824 else 17600777029632))) else (if idx < 30 then (if idx < 28 then 146940838380336 else (if idx < 29 then 106791714521770 else 37392531065504)) else (if idx < 31 then 98993161324131 else (if idx < 32 then 41878733337344 else 99593196286225)))) else (if idx < 39 then (if idx < 36 then (if idx < 34 then 106680279042048 else (if idx < 35 then 185841362338064 else 158368332251392)) else (if idx < 37 then 162939136395127 else (if idx < 38 then 73682588534640 else 52815217035008))) else (if idx < 42 then (if idx < 40 then 58772711708256 else (if idx < 41 then 7325107066641 else 186926113554704)) else (if idx < 43 then 89282073213606 else (if idx < 44 then 168524136064000 else 58348095679146)))))) else (if idx < 67 then (if idx < 56 then (if idx < 50 then (if idx < 47 then (if idx < 46 then 109995455808768 else 89075746998944) else (if idx < 48 then 17630842849792 else (if idx < 49 then 106812643049745 else 19808663372048))) else (if idx < 53 then (if idx < 51 then 35188675444992 else (if idx < 52 then 79266342963336 else 7933896704819)) else (if idx < 54 then 108860518172208 else (if idx < 55 then 99121169332896 else 111738828620339)))) else (if idx < 61 then (if idx < 58 then (if idx < 57 then 40159997556872 else 63778389492528) else (if idx < 59 then 79197589932160 else (if idx < 60 then 140780445370368 else 79522679894835))) else (if idx < 64 then (if idx < 62 then 146256796255024 else (if idx < 63 then 87965228335872 else 59876451161425)) else (if idx < 65 then 74102434539861 else (if idx < 66 then 129755534459984 else 99512551112980))))) else (if idx < 78 then (if idx < 72 then (if idx < 69 then (if idx < 68 then 125636807600042 else 79544577037926) else (if idx < 70 then 92404344030880 else (if idx < 71 then 146263502816864 else 88003880945152))) else (if idx < 75 then (if idx < 73 then 27778064279688 else (if idx < 74 then 162767725529216 else 70390225307648)) else (if idx < 76 then 147413615610261 else (if idx < 77 then 45377744177766 else 145170974114144)))) else (if idx < 84 then (if idx < 81 then (if idx < 79 then 89146733537140 else (if idx < 80 then 77696288242022 else 178612243871061)) else (if idx < 82 then 98978337325664 else (if idx < 83 then 42908611970384 else 123175370228992))) else (if idx < 87 then (if idx < 85 then 20083594918297 else (if idx < 86 then 39587529820560 else 70381636421888)) else (if idx < 88 then 166110316069960 else (if idx < 89 then 37660460946295 else 22016545065584))))))) else (if idx < 135 then (if idx < 112 then (if idx < 101 then (if idx < 95 then (if idx < 92 then (if idx < 91 then 19877402913175 else 76593112286515) else (if idx < 93 then 186303760442436 else (if idx < 94 then 81374875748144 else 166041563038784))) else (if idx < 98 then (if idx < 96 then 123183959114752 else (if idx < 97 then 146940316169557 else 98970283214160)) else (if idx < 99 then 175943338427648 else (if idx < 100 then 343714828297 else 92943757650568)))) else (if idx < 106 then (if idx < 103 then (if idx < 102 then 184745610316416 else 79381624686722) else (if idx < 104 then 144480898951202 else (if idx < 105 then 166239201858355 else 6598144163872))) else (if idx < 109 then (if idx < 107 then 126483568853808 else (if idx < 108 then 52793739051776 else 99606843253282)) else (if idx < 110 then 185853437936160 else (if idx < 111 then 158355450495488 else 99056986759720))))) else (if idx < 123 then (if idx < 117 then (if idx < 114 then (if idx < 113 then 129837991957401 else 89078428664208) else (if idx < 115 then 39879175263029 else (if idx < 116 then 182128094712115 else 146932855480866))) else (if idx < 120 then (if idx < 118 then 28600197253424 else (if idx < 119 then 98988267274784 else 175956222280192)) else (if idx < 121 then 178641991772058 else (if idx < 122 then 42903508486560 else 123162484279808)))) else (if idx < 129 then (if idx < 126 then (if idx < 124 then 117034472440345 else (if idx < 125 then 36941660967490 else 97888214779424)) else (if idx < 127 then 549772623877 else (if idx < 128 then 98176871696706 else 116701067174777))) else (if idx < 132 then (if idx < 130 then 22025937619488 else (if idx < 131 then 178160888317840 else 35205853219072)) else (if idx < 133 then 146927503500153 else (if idx < 134 then 98971355056016 else 175960521443584)))))) else (if idx < 157 then (if idx < 146 then (if idx < 140 then (if idx < 137 then (if idx < 136 then 166748350399000 else 114718904316471) else (if idx < 138 then 163832339564144 else (if idx < 139 then 19961435458135 else 77043126137699))) else (if idx < 143 then (if idx < 141 then 126889040627076 else (if idx < 142 then 71506921458224 else 59418726369344)) else (if idx < 144 then 105587480200192 else (if idx < 145 then 166264736782402 else 126479810757664)))) else (if idx < 151 then (if idx < 148 then (if idx < 147 then 52802328986112 else 127145266791816) else (if idx < 149 then 111740596885281 else (if idx < 150 then 116591720727824 else 166677036881987))) else (if idx < 154 then (if idx < 152 then 6687272106595 else (if idx < 153 then 59464249386906 else 141862775489328)) else (if idx < 155 then 106659345205664 else (if idx < 156 then 17630842849792 else 126874225637797))))) else (if idx < 168 then (if idx < 162 then (if idx < 159 then (if idx < 158 then 59387861731920 else 105574598444288) else (if idx < 160 then 19834818815545 else (if idx < 161 then 55257247418646 else 39592086995808))) else (if idx < 165 then (if idx < 163 then 59547041474455 else (if idx < 164 then 87993485972290 else 186342109690277)) else (if idx < 166 then 158369410517024 else (if idx < 167 then 166036726024784 else 123175370228992)))) else (if idx < 174 then (if idx < 171 then (if idx < 169 then 59482132948057 else (if idx < 170 then 106670621066640 else 17605081434368)) else (if idx < 172 then 166185613816131 else (if idx < 173 then 11624437600866 else 150673360749344))) else (if idx < 177 then (if idx < 175 then 20217856411030 else (if idx < 176 then 81983705532456 else 106808144454745)) else (if idx < 178 then 80307568248704 else (if idx < 179 then 19805438870928 else 35205853219072))))))))

def f11DesInv (k r c : Nat) : Nat :=
  (f11DesInvRow (k * 12 + r) >>> (4 * c)) &&& 15

def f11IntInvRow (idx : Nat) : Nat :=
  (if idx < 60 then (if idx < 30 then (if idx < 15 then (if idx < 7 then (if idx < 3 then (if idx < 1 then 825757971 else (if idx < 2 then 1394975238 else 1463969809)) else (if idx < 5 then (if idx < 4 then 122947685 else 73668742) else (if idx < 6 then 899321897 else 1140983702))) else (if idx < 11 then (if idx < 9 then (if idx < 8 then 2861569161 else 693645458) else (if idx < 10 then 295056441 else 1392908903)) else (if idx < 13 then (if idx < 12 then 2035390530 else 1114060969) else (if idx < 14 then 1610754576 else 2527347363)))) else (if idx < 22 then (if idx < 18 then (if idx < 16 then 1679099991 else (if idx < 17 then 943020033 else 1465346086)) else (if idx < 20 then (if idx < 19 then 1515403312 else 141927270) else (if idx < 21 then 54731397 else 813052182))) else (if idx < 26 then (if idx < 24 then (if idx < 23 then 1231119690 else 2787334680) else (if idx < 25 then 354682914 else 1720128370)) else (if idx < 28 then (if idx < 27 then 2315815457 else 2250405273) else (if idx < 29 then 2006282357 else 1980402297))))) else (if idx < 45 then (if idx < 37 then (if idx < 33 then (if idx < 31 then 373516100 else (if idx < 32 then 695808856 else 421669258)) else (if idx < 35 then (if idx < 34 then 1242929510 else 106596122) else (if idx < 36 then 1984078343 else 413833030))) else (if idx < 41 then (if idx < 39 then (if idx < 38 then 137987626 else 690464785) else (if idx < 40 then 395990338 else 1634800153)) else (if idx < 43 then (if idx < 42 then 846688917 else 1128354624) else (if idx < 44 then 1397188904 else 1092961569)))) else (if idx < 52 then (if idx < 48 then (if idx < 46 then 1361278021 else (if idx < 47 then 1202010521 else 596801335)) else (if idx < 50 then (if idx < 49 then 1980127587 else 2493998629) else (if idx < 51 then 1446679204 else 1637458598))) else (if idx < 56 then (if idx < 54 then (if idx < 53 then 1083704832 else 1110544961) else (if idx < 55 then 2236822384 else 361915288)) else (if idx < 58 then (if idx < 57 then 1436026672 else 1342333473) else (if idx < 59 then 72964119 else 379668514)))))) else (if idx < 90 then (if idx < 75 then (if idx < 67 then (if idx < 63 then (if idx < 61 then 2719191322 else (if idx < 62 then 1218843270 else 1487364098)) else (if idx < 65 then (if idx < 64 then 1247901241 else 824264467) else (if idx < 66 then 1679959361 else 908735013))) else (if idx < 71 then (if idx < 69 then (if idx < 68 then 1234377113 else 2539734675) else (if idx < 70 then 1245226386 else 21572137)) else (if idx < 73 then (if idx < 72 then 1719665936 else 93618740) else (if idx < 74 then 1452422736 else 2038081945)))) else (if idx < 82 then (if idx < 78 then (if idx < 76 then 706914882 else (if idx < 77 then 544560645 else 2036768822)) else (if idx < 80 then (if idx < 79 then 2206496819 else 1180058134) else (if idx < 81 then 1217831699 else 594838074))) else (if idx < 86 then (if idx < 84 then (if idx < 83 then 2000197904 else 1398806634) else (if idx < 85 then 1083704832 else 2438611976)) else (if idx < 88 then (if idx < 87 then 1903662728 else 1469670944) else (if idx < 89 then 805770338 else 122755674))))) else (if idx < 105 then (if idx < 97 then (if idx < 93 then (if idx < 91 then 891969690 else (if idx < 92 then 1967621220 else 563298579)) else (if idx < 95 then (if idx < 94 then 1770367494 else 1403660586) else (if idx < 96 then 713561411 else 2282752052))) else (if idx < 101 then (if idx < 99 then (if idx < 98 then 1251576085 else 2309525889) else (if idx < 100 then 910526601 else 73628048)) else (if idx < 103 then (if idx < 102 then 388650244 else 878148103) else (if idx < 104 then 1917474965 else 1447134117)))) else (if idx < 112 then (if idx < 108 then (if idx < 106 then 2258272864 else (if idx < 107 then 591612435 else 1700426632)) else (if idx < 110 then (if idx < 109 then 1687765641 else 1967732226) else (if idx < 111 then 2709082433 else 1379427106))) else (if idx < 116 then (if idx < 114 then (if idx < 113 then 2592641128 else 2269655209) else (if idx < 115 then 42157173 else 2192004739)) else (if idx < 118 then (if idx < 117 then 4233222 else 594043238) else (if idx < 119 then 672750185 else 75104553)))))))

def f11IntInv (k r c : Nat) : Nat :=
  (f11IntInvRow (k * 8 + r) >>> (4 * c)) &&& 15

def f11IntPivPack (k : Nat) : Nat :=
  (if k < 7 then (if k < 3 then (if k < 1 then 2825138704 else (if k < 2 then 2825138704 else 2825138704)) else (if k < 5 then (if k < 4 then 2825138704 else 2825138704) else (if k < 6 then 2825138704 else 2825138704))) else (if k < 11 then (if k < 9 then (if k < 8 then 2825138704 else 2825138704) else (if k < 10 then 2825138704 else 2825138704)) else (if k < 13 then (if k < 12 then 2825138704 else 2825138704) else (if k < 14 then 2825138704 else 2825138704))))

def f11IntPiv (k j : Nat) : Nat :=
  (f11IntPivPack k >>> (4 * j)) &&& 15

def f11FlagVInvRow (idx : Nat) : Nat :=
  (if idx < 75 then (if idx < 37 then (if idx < 18 then (if idx < 9 then (if idx < 4 then (if idx < 2 then (if idx < 1 then 468121 else 394336) else (if idx < 3 then 655414 else 551296)) else (if idx < 6 then (if idx < 5 then 65608 else 170328) else (if idx < 7 then 168340 else (if idx < 8 then 327770 else 202630)))) else (if idx < 13 then (if idx < 11 then (if idx < 10 then 393252 else 9272) else (if idx < 12 then 614996 else 458788)) else (if idx < 15 then (if idx < 14 then 423290 else 262234) else (if idx < 16 then 208899 else (if idx < 17 then 293169 else 524385))))) else (if idx < 27 then (if idx < 22 then (if idx < 20 then (if idx < 19 then 530274 else 196626) else (if idx < 21 then 226920 else 692610)) else (if idx < 24 then (if idx < 23 then 131144 else 158055) else (if idx < 25 then 589878 else (if idx < 26 then 225322 else 479560)))) else (if idx < 32 then (if idx < 29 then (if idx < 28 then 131156 else 293491) else (if idx < 30 then 655463 else (if idx < 31 then 689056 else 140115))) else (if idx < 34 then (if idx < 33 then 589946 else 227882) else (if idx < 35 then 65620 else (if idx < 36 then 551074 else 414116)))))) else (if idx < 56 then (if idx < 46 then (if idx < 41 then (if idx < 39 then (if idx < 38 then 655379 else 305210) else (if idx < 40 then 393346 else 223348)) else (if idx < 43 then (if idx < 42 then 467841 else 196776) else (if idx < 44 then 206418 else (if idx < 45 then 262293 else 206674)))) else (if idx < 51 then (if idx < 48 then (if idx < 47 then 231978 else 327829) else (if idx < 49 then 361074 else (if idx < 50 then 196673 else 423721))) else (if idx < 53 then (if idx < 52 then 529504 else 606514) else (if idx < 54 then 198480 else (if idx < 55 then 227977 else 477010))))) else (if idx < 65 then (if idx < 60 then (if idx < 58 then (if idx < 57 then 411991 else 669095) else (if idx < 59 then 540978 else 82786)) else (if idx < 62 then (if idx < 61 then 14183 else 524869) else (if idx < 63 then 693770 else (if idx < 64 then 603559 else 418819)))) else (if idx < 70 then (if idx < 67 then (if idx < 66 then 297092 else 197941) else (if idx < 68 then 173173 else (if idx < 69 then 432746 else 170042))) else (if idx < 72 then (if idx < 71 then 140801 else 96163) else (if idx < 73 then 141857 else (if idx < 74 then 632869 else 619129))))))) else (if idx < 112 then (if idx < 93 then (if idx < 84 then (if idx < 79 then (if idx < 77 then (if idx < 76 then 218410 else 337496) else (if idx < 78 then 282948 else 435555)) else (if idx < 81 then (if idx < 80 then 551543 else 218280) else (if idx < 82 then 496455 else (if idx < 83 then 341520 else 160914)))) else (if idx < 88 then (if idx < 86 then (if idx < 85 then 608336 else 217974) else (if idx < 87 then 553554 else 615430)) else (if idx < 90 then (if idx < 89 then 103203 else 103945) else (if idx < 91 then 274778 else (if idx < 92 then 222851 else 168314))))) else (if idx < 102 then (if idx < 97 then (if idx < 95 then (if idx < 94 then 434518 else 160313) else (if idx < 96 then 549408 else 109078)) else (if idx < 99 then (if idx < 98 then 10522 else 606874) else (if idx < 100 then 160914 else (if idx < 101 then 406038 else 328522)))) else (if idx < 107 then (if idx < 104 then (if idx < 103 then 104294 else 399473) else (if idx < 105 then 9301 else (if idx < 106 then 358696 else 682394))) else (if idx < 109 then (if idx < 108 then 215652 else 405782) else (if idx < 110 then 693897 else (if idx < 111 then 698710 else 169811)))))) else (if idx < 131 then (if idx < 121 then (if idx < 116 then (if idx < 114 then (if idx < 113 then 616866 else 202026) else (if idx < 115 then 104515 else 399729)) else (if idx < 118 then (if idx < 117 then 500535 else 231251) else (if idx < 119 then 90657 else (if idx < 120 then 364914 else 274513)))) else (if idx < 126 then (if idx < 123 then (if idx < 122 then 484936 else 262994) else (if idx < 124 then 530998 else (if idx < 125 then 328983 else 623896))) else (if idx < 128 then (if idx < 127 then 198713 else 19061) else (if idx < 129 then 529282 else (if idx < 130 then 94534 else 145207))))) else (if idx < 140 then (if idx < 135 then (if idx < 133 then (if idx < 132 then 100132 else 17946) else (if idx < 134 then 336553 else 432214)) else (if idx < 137 then (if idx < 136 then 531040 else 677015) else (if idx < 138 then 595205 else (if idx < 139 then 288389 else 94722)))) else (if idx < 145 then (if idx < 142 then (if idx < 141 then 289032 else 292673) else (if idx < 143 then 546466 else (if idx < 144 then 672168 else 95285))) else (if idx < 147 then (if idx < 146 then 625011 else 485026) else (if idx < 148 then 66099 else (if idx < 149 then 237972 else 1126))))))))

def f11FlagVInv (k r c : Nat) : Nat :=
  (f11FlagVInvRow (k * 5 + r) >>> (4 * c)) &&& 15

def f11FlagVPivPack (k : Nat) : Nat :=
  (if k < 15 then (if k < 7 then (if k < 3 then (if k < 1 then 274960 else (if k < 2 then 274960 else 274960)) else (if k < 5 then (if k < 4 then 274960 else 274960) else (if k < 6 then 274960 else 274960))) else (if k < 11 then (if k < 9 then (if k < 8 then 274960 else 274960) else (if k < 10 then 274960 else 274960)) else (if k < 13 then (if k < 12 then 274960 else 274960) else (if k < 14 then 274960 else 274960)))) else (if k < 22 then (if k < 18 then (if k < 16 then 274960 else (if k < 17 then 274960 else 274960)) else (if k < 20 then (if k < 19 then 274960 else 274960) else (if k < 21 then 274960 else 274960))) else (if k < 26 then (if k < 24 then (if k < 23 then 274960 else 274960) else (if k < 25 then 274960 else 274960)) else (if k < 28 then (if k < 27 then 274960 else 274960) else (if k < 29 then 274960 else 274960)))))

def f11FlagVPiv (k j : Nat) : Nat :=
  (f11FlagVPivPack k >>> (4 * j)) &&& 15

def f11FlagUInvRow (idx : Nat) : Nat :=
  (if idx < 75 then (if idx < 37 then (if idx < 18 then (if idx < 9 then (if idx < 4 then (if idx < 2 then (if idx < 1 then 256 else 41315) else (if idx < 3 then 5508 else 657168)) else (if idx < 6 then (if idx < 5 then 66128 else 256) else (if idx < 7 then 22949 else (if idx < 8 then 26690 else 329872)))) else (if idx < 13 then (if idx < 11 then (if idx < 10 then 393600 else 256) else (if idx < 12 then 30786 else 18853)) else (if idx < 15 then (if idx < 14 then 459136 else 264336) else (if idx < 16 then 256 else (if idx < 17 then 33302 else 13345))))) else (if idx < 27 then (if idx < 22 then (if idx < 20 then (if idx < 19 then 525088 else 198208) else (if idx < 21 then 256 else 9604)) else (if idx < 24 then (if idx < 23 then 37219 else 131664) else (if idx < 25 then 591632 else (if idx < 26 then 256 else 10890)))) else (if idx < 32 then (if idx < 29 then (if idx < 28 then 41265 else 133542) else (if idx < 30 then 655893 else (if idx < 31 then 256 else 37779))) else (if idx < 34 then (if idx < 33 then 6794 else 591412) else (if idx < 35 then 68006 else (if idx < 36 then 256 else 41570)))))) else (if idx < 56 then (if idx < 46 then (if idx < 41 then (if idx < 39 then (if idx < 38 then 25925 else 656426) else (if idx < 40 then 395859 else 256)) else (if idx < 43 then (if idx < 42 then 14681 else 18343) else (if idx < 44 then 198545 else (if idx < 45 then 263026 else 256)))) else (if idx < 51 then (if idx < 48 then (if idx < 47 then 22439 else 14376) else (if idx < 49 then 328562 else (if idx < 50 then 198023 else 256))) else (if idx < 53 then (if idx < 52 then 30090 else 22065) else (if idx < 54 then 461320 else (if idx < 55 then 327939 else 256))))) else (if idx < 65 then (if idx < 60 then (if idx < 58 then (if idx < 57 then 14759 else 41314) else (if idx < 59 then 198410 else 655878)) else (if idx < 62 then (if idx < 61 then 256 else 33832) else (if idx < 63 then 6745 else (if idx < 64 then 526338 else 67845)))) else (if idx < 70 then (if idx < 67 then (if idx < 66 then 256 else 18501) else (if idx < 68 then 25994 else (if idx < 69 then 263428 else 395784))) else (if idx < 72 then (if idx < 71 then 256 else 41492) else (if idx < 73 then 18323 else (if idx < 74 then 656385 else 262921))))))) else (if idx < 112 then (if idx < 93 then (if idx < 84 then (if idx < 79 then (if idx < 77 then (if idx < 76 then 256 else 23044) else (if idx < 78 then 28935 else 328215)) else (if idx < 81 then (if idx < 80 then 461220 else 256) else (if idx < 82 then 10241 else (if idx < 83 then 22277 else 132666)))) else (if idx < 88 then (if idx < 86 then (if idx < 85 then 329798 else 256) else (if idx < 87 then 16899 else 41738)) else (if idx < 90 then (if idx < 89 then 264088 else 656769) else (if idx < 91 then 256 else (if idx < 92 then 29702 else 6145))))) else (if idx < 102 then (if idx < 97 then (if idx < 95 then (if idx < 94 then 459637 else 67130) else (if idx < 96 then 256 else 39176)) else (if idx < 99 then (if idx < 98 then 25606 else 590883) else (if idx < 100 then 394101 else (if idx < 101 then 256 else 17299)))) else (if idx < 107 then (if idx < 104 then (if idx < 103 then 34856 else 264272) else (if idx < 105 then 525152 else (if idx < 106 then 256 else 38952))) else (if idx < 109 then (if idx < 108 then 30631 else 590688) else (if idx < 110 then 459904 else (if idx < 111 then 256 else 34727)))))) else (if idx < 131 then (if idx < 121 then (if idx < 116 then (if idx < 114 then (if idx < 113 then 21829 else 525440) else (if idx < 115 then 329232 else 256)) else (if idx < 118 then (if idx < 117 then 21524 else 43658) else (if idx < 119 then 329520 else (if idx < 120 then 655648 else 256)))) else (if idx < 126 then (if idx < 123 then (if idx < 122 then 25925 else 4401) else (if idx < 124 then 394768 else (if idx < 125 then 68240 else 256))) else (if idx < 128 then (if idx < 127 then 42784 else 9360) else (if idx < 129 then 657442 else (if idx < 130 then 131993 else 256))))) else (if idx < 140 then (if idx < 135 then (if idx < 133 then (if idx < 132 then 29008 else 34096) else (if idx < 134 then 461141 else 524595)) else (if idx < 137 then (if idx < 136 then 256 else 8864) else (if idx < 138 then 29504 else (if idx < 139 then 133034 else 460100)))) else (if idx < 145 then (if idx < 142 then (if idx < 141 then 256 else 13456) else (if idx < 143 then 23136 else (if idx < 144 then 197529 else 328294))) else (if idx < 147 then (if idx < 146 then 256 else 27232) else (if idx < 148 then 43280 else (if idx < 149 then 393830 else 656401))))))))

def f11FlagUInv (k r c : Nat) : Nat :=
  (f11FlagUInvRow (k * 5 + r) >>> (4 * c)) &&& 15

def f11FlagUPivPack (k : Nat) : Nat :=
  (if k < 15 then (if k < 7 then (if k < 3 then (if k < 1 then 274960 else (if k < 2 then 274960 else 274960)) else (if k < 5 then (if k < 4 then 274960 else 274960) else (if k < 6 then 274960 else 274960))) else (if k < 11 then (if k < 9 then (if k < 8 then 274960 else 274960) else (if k < 10 then 274960 else 274960)) else (if k < 13 then (if k < 12 then 274960 else 274960) else (if k < 14 then 274960 else 274960)))) else (if k < 22 then (if k < 18 then (if k < 16 then 274960 else (if k < 17 then 274960 else 274960)) else (if k < 20 then (if k < 19 then 274960 else 274960) else (if k < 21 then 274960 else 274960))) else (if k < 26 then (if k < 24 then (if k < 23 then 274960 else 274960) else (if k < 25 then 274960 else 274960)) else (if k < 28 then (if k < 27 then 274960 else 274960) else (if k < 29 then 274960 else 274960)))))

def f11FlagUPiv (k j : Nat) : Nat :=
  (f11FlagUPivPack k >>> (4 * j)) &&& 15

def f11SubPack (idx : Nat) : Nat :=
  (if idx < 7 then (if idx < 3 then (if idx < 1 then 12816 else (if idx < 2 then 16912 else 21008)) else (if idx < 5 then (if idx < 4 then 17168 else 21264) else (if idx < 6 then 21520 else 17184))) else (if idx < 11 then (if idx < 9 then (if idx < 8 then 21280 else 21536) else (if idx < 10 then 21552 else 17185)) else (if idx < 13 then (if idx < 12 then 21281 else 21537) else (if idx < 14 then 21553 else 21554))))
def f11Sub (idx s : Nat) : Nat := (f11SubPack idx >>> (4 * s)) &&& 15
def f11PairPack (idx : Nat) : Nat :=
  (if idx < 15 then (if idx < 7 then (if idx < 3 then (if idx < 1 then 16 else (if idx < 2 then 32 else 48)) else (if idx < 5 then (if idx < 4 then 64 else 80) else (if idx < 6 then 1 else 33))) else (if idx < 11 then (if idx < 9 then (if idx < 8 then 49 else 65) else (if idx < 10 then 81 else 2)) else (if idx < 13 then (if idx < 12 then 18 else 50) else (if idx < 14 then 66 else 82)))) else (if idx < 22 then (if idx < 18 then (if idx < 16 then 3 else (if idx < 17 then 19 else 35)) else (if idx < 20 then (if idx < 19 then 67 else 83) else (if idx < 21 then 4 else 20))) else (if idx < 26 then (if idx < 24 then (if idx < 23 then 36 else 52) else (if idx < 25 then 84 else 5)) else (if idx < 28 then (if idx < 27 then 21 else 37) else (if idx < 29 then 53 else 69)))))
def f11PairI (idx : Nat) : Nat := f11PairPack idx &&& 15
def f11PairJ (idx : Nat) : Nat := (f11PairPack idx >>> 4) &&& 15

def f11Alpha (srv : Nat) : Nat := srv + 1

def f11PV (n r c : Nat) : Nat :=
  sumMod11 3 (fun t => f11ASel n r t * f11V n t c)

def f11PU (n r c : Nat) : Nat :=
  sumMod11 3 (fun t => f11BSel n r t * f11U n t c)

def f11DesEntry (idx row col : Nat) : Nat :=
  let srv := f11Sub idx (row / 3)
  let r := row % 3
  if col < 6 then f11V srv r col else (f11V srv r (col - 6) * f11Alpha srv) % 11

def f11IntSubEntry (idx row j : Nat) : Nat :=
  let srv := f11Sub idx (row / 2)
  let r := row % 2
  let col := f11IntPiv idx j
  if col < 6 then f11PU srv r col else (f11PU srv r (col - 6) * f11Alpha srv) % 11

def f11FlagVSubEntry (idx row j : Nat) : Nat :=
  let col := f11FlagVPiv idx j
  if row < 2 then f11PV (f11PairI idx) row col else f11V (f11PairJ idx) (row - 2) col

def f11FlagUSubEntry (idx row j : Nat) : Nat :=
  let col := f11FlagUPiv idx j
  if row < 2 then f11PU (f11PairI idx) row col else f11U (f11PairJ idx) (row - 2) col

def checkInvMod11 (n : Nat) (A B : Nat → Nat → Nat) : Bool :=
  allBelow n fun i =>
    allBelow n fun j =>
      sumMod11 n (fun t => A i t * B t j) == (if i == j then 1 else 0)

def checkF11ByzantineRate25 : Bool :=
  allBelow 15 (fun idx => checkInvMod11 12 (f11DesEntry idx) (f11DesInv idx)) &&
  allBelow 15 (fun idx => checkInvMod11 8 (f11IntSubEntry idx) (f11IntInv idx)) &&
  allBelow 30 (fun idx => checkInvMod11 5 (f11FlagVSubEntry idx) (f11FlagVInv idx)) &&
  allBelow 30 (fun idx => checkInvMod11 5 (f11FlagUSubEntry idx) (f11FlagUInv idx))

theorem f11_byzantine_rate25_certified : checkF11ByzantineRate25 = true := by decide

-- ============================================================================
-- Part 2: Exact Pure-Integer Unconditioned Shannon+Ingleton Polymatroid (Scale 128)
-- ============================================================================

def hUncondAt (r : Nat) : Nat :=
  (if r < 165 then (if r < 82 then (if r < 41 then (if r < 20 then (if r < 10 then (if r < 5 then (if r < 2 then (if r < 1 then 0 else 64) else (if r < 3 then 128 else (if r < 4 then 128 else 128))) else (if r < 7 then (if r < 6 then 64 else 128) else (if r < 8 then 192 else (if r < 9 then 192 else 128)))) else (if r < 15 then (if r < 12 then (if r < 11 then 192 else 256) else (if r < 13 then 128 else (if r < 14 then 192 else 128))) else (if r < 17 then (if r < 16 then 128 else 192) else (if r < 18 then 192 else (if r < 19 then 192 else 192))))) else (if r < 30 then (if r < 25 then (if r < 22 then (if r < 21 then 256 else 256) else (if r < 23 then 192 else (if r < 24 then 256 else 192))) else (if r < 27 then (if r < 26 then 256 else 256) else (if r < 28 then 256 else (if r < 29 then 256 else 256)))) else (if r < 35 then (if r < 32 then (if r < 31 then 256 else 256) else (if r < 33 then 256 else (if r < 34 then 256 else 256))) else (if r < 38 then (if r < 36 then 52 else (if r < 37 then 116 else 160)) else (if r < 39 then 160 else (if r < 40 then 116 else 180)))))) else (if r < 61 then (if r < 51 then (if r < 46 then (if r < 43 then (if r < 42 then 224 else 160) else (if r < 44 then 224 else (if r < 45 then 160 else 180))) else (if r < 48 then (if r < 47 then 224 else 224) else (if r < 49 then 224 else (if r < 50 then 256 else 224)))) else (if r < 56 then (if r < 53 then (if r < 52 then 256 else 256) else (if r < 54 then 256 else (if r < 55 then 256 else 104))) else (if r < 58 then (if r < 57 then 162 else 192) else (if r < 59 then 162 else (if r < 60 then 210 else 192))))) else (if r < 71 then (if r < 66 then (if r < 63 then (if r < 62 then 214 else 240) else (if r < 64 then 240 else (if r < 65 then 256 else 156))) else (if r < 68 then (if r < 67 then 188 else 208) else (if r < 69 then 240 else (if r < 70 then 208 else 96)))) else (if r < 76 then (if r < 73 then (if r < 72 then 160 else 160) else (if r < 74 then 160 else (if r < 75 then 160 else 224))) else (if r < 79 then (if r < 77 then 224 else (if r < 78 then 192 else 256)) else (if r < 80 then 192 else (if r < 81 then 224 else 224))))))) else (if r < 123 then (if r < 102 then (if r < 92 then (if r < 87 then (if r < 84 then (if r < 83 then 224 else 256) else (if r < 85 then 256 else (if r < 86 then 256 else 256))) else (if r < 89 then (if r < 88 then 256 else 256) else (if r < 90 then 256 else (if r < 91 then 148 else 192)))) else (if r < 97 then (if r < 94 then (if r < 93 then 192 else 201) else (if r < 95 then 240 else (if r < 96 then 224 else 240))) else (if r < 99 then (if r < 98 then 240 else 256) else (if r < 100 then 256 else (if r < 101 then 182 else 208))))) else (if r < 112 then (if r < 107 then (if r < 104 then (if r < 103 then 224 else 240) else (if r < 105 then 208 else (if r < 106 then 192 else 192))) else (if r < 109 then (if r < 108 then 192 else 240) else (if r < 110 then 240 else (if r < 111 then 256 else 240)))) else (if r < 117 then (if r < 114 then (if r < 113 then 240 else 256) else (if r < 115 then 256 else (if r < 116 then 208 else 208))) else (if r < 120 then (if r < 118 then 240 else (if r < 119 then 240 else 208)) else (if r < 121 then 208 else (if r < 122 then 208 else 240)))))) else (if r < 144 then (if r < 133 then (if r < 128 then (if r < 125 then (if r < 124 then 240 else 208) else (if r < 126 then 208 else (if r < 127 then 96 else 160))) else (if r < 130 then (if r < 129 then 192 else 192) else (if r < 131 then 160 else (if r < 132 then 224 else 256)))) else (if r < 138 then (if r < 135 then (if r < 134 then 160 else 224) else (if r < 136 then 160 else (if r < 137 then 224 else 256))) else (if r < 141 then (if r < 139 then 256 else (if r < 140 then 224 else 256)) else (if r < 142 then 224 else (if r < 143 then 256 else 256))))) else (if r < 154 then (if r < 149 then (if r < 146 then (if r < 145 then 256 else 256) else (if r < 147 then 148 else (if r < 148 then 201 else 224))) else (if r < 151 then (if r < 150 then 192 else 240) else (if r < 152 then 192 else (if r < 153 then 240 else 256)))) else (if r < 159 then (if r < 156 then (if r < 155 then 240 else 256) else (if r < 157 then 194 else (if r < 158 then 226 else 224))) else (if r < 162 then (if r < 160 then 256 else (if r < 161 then 240 else 192)) else (if r < 163 then 224 else (if r < 164 then 224 else 224)))))))) else (if r < 247 then (if r < 206 then (if r < 185 then (if r < 175 then (if r < 170 then (if r < 167 then (if r < 166 then 256 else 224) else (if r < 168 then 256 else (if r < 169 then 256 else 256))) else (if r < 172 then (if r < 171 then 256 else 220) else (if r < 173 then 240 else (if r < 174 then 240 else 256)))) else (if r < 180 then (if r < 177 then (if r < 176 then 240 else 240) else (if r < 178 then 240 else (if r < 179 then 256 else 256))) else (if r < 182 then (if r < 181 then 240 else 240) else (if r < 183 then 192 else (if r < 184 then 240 else 256))))) else (if r < 195 then (if r < 190 then (if r < 187 then (if r < 186 then 192 else 240) else (if r < 188 then 192 else (if r < 189 then 240 else 256))) else (if r < 192 then (if r < 191 then 240 else 256) else (if r < 193 then 224 else (if r < 194 then 256 else 224)))) else (if r < 200 then (if r < 197 then (if r < 196 then 256 else 256) else (if r < 198 then 240 else (if r < 199 then 256 else 240))) else (if r < 203 then (if r < 201 then 256 else (if r < 202 then 256 else 256)) else (if r < 204 then 224 else (if r < 205 then 256 else 224)))))) else (if r < 226 then (if r < 216 then (if r < 211 then (if r < 208 then (if r < 207 then 256 else 256) else (if r < 209 then 256 else (if r < 210 then 256 else 128))) else (if r < 213 then (if r < 212 then 192 else 192) else (if r < 214 then 192 else (if r < 215 then 192 else 256)))) else (if r < 221 then (if r < 218 then (if r < 217 then 256 else 192) else (if r < 219 then 256 else (if r < 220 then 192 else 256))) else (if r < 223 then (if r < 222 then 256 else 256) else (if r < 224 then 256 else (if r < 225 then 256 else 256))))) else (if r < 236 then (if r < 231 then (if r < 228 then (if r < 227 then 256 else 256) else (if r < 229 then 256 else (if r < 230 then 256 else 180))) else (if r < 233 then (if r < 232 then 224 else 224) else (if r < 234 then 224 else (if r < 235 then 256 else 224)))) else (if r < 241 then (if r < 238 then (if r < 237 then 256 else 256) else (if r < 239 then 256 else (if r < 240 then 256 else 214))) else (if r < 244 then (if r < 242 then 240 else (if r < 243 then 240 else 256)) else (if r < 245 then 240 else (if r < 246 then 224 else 224))))))) else (if r < 288 then (if r < 267 then (if r < 257 then (if r < 252 then (if r < 249 then (if r < 248 then 224 else 256) else (if r < 250 then 256 else (if r < 251 then 256 else 256))) else (if r < 254 then (if r < 253 then 256 else 256) else (if r < 255 then 256 else (if r < 256 then 240 else 240)))) else (if r < 262 then (if r < 259 then (if r < 258 then 256 else 256) else (if r < 260 then 240 else (if r < 261 then 240 else 240))) else (if r < 264 then (if r < 263 then 256 else 256) else (if r < 265 then 240 else (if r < 266 then 240 else 224))))) else (if r < 277 then (if r < 272 then (if r < 269 then (if r < 268 then 256 else 256) else (if r < 270 then 224 else (if r < 271 then 256 else 224))) else (if r < 274 then (if r < 273 then 256 else 256) else (if r < 275 then 256 else (if r < 276 then 256 else 240)))) else (if r < 282 then (if r < 279 then (if r < 278 then 256 else 240) else (if r < 280 then 256 else (if r < 281 then 256 else 256))) else (if r < 285 then (if r < 283 then 256 else (if r < 284 then 256 else 256)) else (if r < 286 then 256 else (if r < 287 then 256 else 240)))))) else (if r < 309 then (if r < 298 then (if r < 293 then (if r < 290 then (if r < 289 then 256 else 240) else (if r < 291 then 256 else (if r < 292 then 256 else 256))) else (if r < 295 then (if r < 294 then 256 else 256) else (if r < 296 then 256 else (if r < 297 then 256 else 256)))) else (if r < 303 then (if r < 300 then (if r < 299 then 256 else 256) else (if r < 301 then 256 else (if r < 302 then 256 else 256))) else (if r < 306 then (if r < 304 then 256 else (if r < 305 then 256 else 256)) else (if r < 307 then 256 else (if r < 308 then 256 else 256))))) else (if r < 319 then (if r < 314 then (if r < 311 then (if r < 310 then 256 else 256) else (if r < 312 then 256 else (if r < 313 then 256 else 256))) else (if r < 316 then (if r < 315 then 256 else 256) else (if r < 317 then 256 else (if r < 318 then 256 else 256)))) else (if r < 324 then (if r < 321 then (if r < 320 then 256 else 256) else (if r < 322 then 256 else (if r < 323 then 256 else 256))) else (if r < 327 then (if r < 325 then 256 else (if r < 326 then 256 else 256)) else (if r < 328 then 256 else (if r < 329 then 256 else 256)))))))))

def sort4 (a b c d : Nat) : Nat × Nat × Nat × Nat :=
  let (a, b) := if a ≤ b then (a, b) else (b, a)
  let (c, d) := if c ≤ d then (c, d) else (d, c)
  let (a, c) := if a ≤ c then (a, c) else (c, a)
  let (b, d) := if b ≤ d then (b, d) else (d, b)
  let (b, c) := if b ≤ c then (b, c) else (c, b)
  (a, b, c, d)

def colexRank4 (a b c d : Nat) : Nat :=
  let (s0, s1, s2, s3) := sort4 a b c d
  let c2 := ((s1 + 1) * s1) / 2
  let c3 := ((s2 + 2) * (s2 + 1) * s2) / 6
  let c4 := ((s3 + 3) * (s3 + 2) * (s3 + 1) * s3) / 24
  s0 + c2 + c3 + c4

def serverState (mask srv : Nat) : Nat :=
  ((mask >>> srv) &&& 1) ||| (((mask >>> (4 + srv)) &&& 1) <<< 1) ||| (((mask >>> (8 + srv)) &&& 1) <<< 2)

def hUncond (mask : Nat) : Nat :=
  hUncondAt (colexRank4 (serverState mask 0) (serverState mask 1) (serverState mask 2) (serverState mask 3))

def bitsFromStates (s0 s1 s2 s3 : Nat) : Nat :=
  let put (srv st : Nat) : Nat :=
    ((st &&& 1) <<< srv) ||| (((st >>> 1) &&& 1) <<< (4 + srv)) ||| (((st >>> 2) &&& 1) <<< (8 + srv))
  put 0 s0 ||| put 1 s1 ||| put 2 s2 ||| put 3 s3

def checkAllOrbitMonotone : Bool :=
  allBelow 12 fun i => hUncond (4095 ^^^ (1 <<< i)) ≤ hUncond 4095

def checkSubmodAtMask (m : Nat) : Bool :=
  allBelow 12 fun i =>
    let bi := 1 <<< i
    if (m &&& bi) != 0 then true
    else
      allBelow i fun j =>
        let bj := 1 <<< j
        if (m &&& bj) != 0 then true
        else hUncond m + hUncond (m ||| bi ||| bj) ≤ hUncond (m ||| bi) + hUncond (m ||| bj)

def checkAll330OrbitsSubmod : Bool :=
  allBelow 8 fun s3 =>
    allBelow (s3 + 1) fun s2 =>
      allBelow (s2 + 1) fun s1 =>
        allBelow (s1 + 1) fun s0 =>
          checkSubmodAtMask (bitsFromStates s0 s1 s2 s3)

def checkPIREqualities : Bool :=
  let eqBase :=
    hUncond 0 == 0 &&
    hUncond 1 == 64 && hUncond 3 == 128 && hUncond 15 == 128 &&
    hUncond 16 == 64 && hUncond 48 == 128 && hUncond 240 == 128 &&
    hUncond 255 == 256 &&
    hUncond (1 ||| 16 ||| 256) == hUncond (1 ||| 16) &&
    hUncond (15 ||| 3840) == hUncond 3840 &&
    hUncond 256 == 52 && hUncond 3840 == 208
  let checkPrivA (aMask : Nat) : Bool :=
    allBelow 16 fun sMask =>
      allBelow 16 fun tMask =>
        hUncond (sMask ||| (tMask <<< 4) ||| (aMask <<< 8)) ==
        hUncond (tMask ||| (sMask <<< 4) ||| (aMask <<< 8))
  eqBase && checkPrivA 0 && checkPrivA 1 && checkPrivA 3

def checkAll1485SingletonIngletons : Bool :=
  allBelow 12 fun b =>
    allBelow b fun a =>
      allBelow 12 fun d =>
        if d == a || d == b then true
        else
          allBelow d fun c =>
            if c == a || c == b then true
            else
              let A := 1 <<< a; let B := 1 <<< b; let C := 1 <<< c; let D := 1 <<< d
              hUncond A + hUncond B + hUncond (C ||| D) + hUncond (A ||| B ||| C) + hUncond (A ||| B ||| D) ≤
              hUncond (A ||| B) + hUncond (A ||| C) + hUncond (A ||| D) + hUncond (B ||| C) + hUncond (B ||| D)

theorem h_uncond_monotone_certified : checkAllOrbitMonotone = true := by decide
theorem h_uncond_submod_certified : checkAll330OrbitsSubmod = true := by decide
theorem h_uncond_pir_eqs_certified : checkPIREqualities = true := by decide
theorem h_uncond_singleton_ingletons_certified : checkAll1485SingletonIngletons = true := by decide

end
end TriadFrontier.PIRCertificates

