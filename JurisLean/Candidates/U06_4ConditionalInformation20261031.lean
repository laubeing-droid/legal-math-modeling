import Mathlib
import JurisLean.External.GameTheory.Math.Probability

noncomputable section

open scoped BigOperators

namespace JurisLean.Candidates.U06_4ConditionalInformation20261031

open Math.Probability

variable {О© A Y : Type} [Fintype О©] [Fintype Y] [DecidableEq Y]

def fiberWeight (P : PMF О©) (obs : О© в†’ Y) (y : Y) (w : О©) : в„ќ :=
  if obs w = y then (P w).toReal else 0

def signalMass (P : PMF О©) (obs : О© в†’ Y) (y : Y) : в„ќ :=
  в€‘ w, fiberWeight P obs y w

private theorem fiberWeight_nonneg (P : PMF О©) (obs : О© в†’ Y) (y : Y) (w : О©) :
    0 в‰¤ fiberWeight P obs y w := by
  unfold fiberWeight
  split_ifs
  В· exact ENNReal.toReal_nonneg
  В· exact le_rfl

private theorem signalMass_nonneg (P : PMF О©) (obs : О© в†’ Y) (y : Y) :
    0 в‰¤ signalMass P obs y :=
  Finset.sum_nonneg (fun w _ => fiberWeight_nonneg P obs y w)

def signalLaw (P : PMF О©) (obs : О© в†’ Y) : PMF Y := PMF.map obs P

private theorem signal_law_mass (P : PMF О©) (obs : О© в†’ Y) (y : Y) :
    (signalLaw P obs y).toReal = signalMass P obs y := by
  classical
  rw [signalLaw, PMF.map_apply, tsum_fintype]
  calc
    _ = (в€‘ w : О©, if y = obs w then P w else 0).toReal := by
      apply congrArg (fun value : ENNReal => value.toReal)
      apply Finset.sum_congr rfl
      intro w _
      by_cases same : y = obs w <;> simp [same]
    _ = в€‘ w : О©, (if y = obs w then P w else 0).toReal :=
      ENNReal.toReal_sum (s := Finset.univ)
        (f := fun w => if y = obs w then P w else 0) (by
          intro w _
          by_cases same : y = obs w <;> simp [same, PMF.apply_ne_top])
    _ = signalMass P obs y := by
      unfold signalMass
      apply Finset.sum_congr rfl
      intro w _
      by_cases same : obs w = y
      В· simp [fiberWeight, same, same.symm]
      В· have reverse : В¬ (y = obs w) := fun h => same h.symm
        simp [fiberWeight, same, reverse]

private theorem signal_expect_eq_sum (P : PMF О©) (obs : О© в†’ Y) (f : Y в†’ в„ќ) :
    expect (signalLaw P obs) f = в€‘ y, signalMass P obs y * f y := by
  rw [expect_eq_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [signal_law_mass]

def conditionalLaw (P : PMF О©) (obs : О© в†’ Y) (y : Y) : Option (PMF О©) := by
  classical
  exact if h : в€ѓ w, obs w = y в€§ w в€€ P.support then
    some (P.filter {w | obs w = y} h)
  else none

/-- This totalization concerns only zero-mass signal fibers, never unknown data
or unresolved labels. Positive fibers use the actual normalized PMF.filter. -/
def conditionalScore (P : PMF О©) (obs : О© в†’ Y)
    (utility : A в†’ О© в†’ в„ќ) (a : A) (y : Y) : в„ќ :=
  match conditionalLaw P obs y with
  | some Q => expect Q (utility a)
  | none => 0

private theorem positive_signal_reachable (P : PMF О©) (obs : О© в†’ Y) (y : Y)
    (positive : 0 < signalMass P obs y) :
    в€ѓ w, obs w = y в€§ w в€€ P.support := by
  classical
  by_contra absent
  have allZero : в€Ђ w, fiberWeight P obs y w = 0 := by
    intro w
    by_cases same : obs w = y
    В· have zero : P w = 0 := by
        by_contra nonzero
        exact absent вџЁw, same, (PMF.mem_support_iff P w).mpr nonzeroвџ©
      simp [fiberWeight, same, zero]
    В· simp [fiberWeight, same]
  have zero : signalMass P obs y = 0 := by
    simp [signalMass, allZero]
  linearity

private theorem fiber_sum_toReal (P : PMF О©) (obs : О© в†’ Y) (y : Y) :
    (в€‘ w, ({z | obs z = y}.indicator (fun z => P z)) w).toReal =
      signalMass P obs y := by
  classsical
  rw [ENNReal.toReal_sum (s := Finset.univ)
    (f := fun w => ({z | obs z = y}.indicator (fun z => P z)) w) (by
      intro w _
      by_cases same : obs w = y <;>
        simp [Set.indicator, same, PMF.apply_ne_top])
  unvold signalMass
  apply Finset.sum_congr rfl
  intro w _
  by_cases same : obs w = y <;> simp [Set.indicator, fiberWeight, same]

private theorem conditional_score_fraction (P : PMF О©) (obs : О© в†’ Y)
    (utility : A в†’ О© в†’ в„ќ) (a : A) (y : Y)
    (positive : 0 < signalMass P obs y):
    conditionalScore P obs utility a y =
      (в€‘ w, fiberWeight P obs y w * utility a w) / signalMass P obs y := by
  classical
  have reachable := positive_signal_reachable P obs y positive
  have point : в€Ђ w,
      ((P.filter {z | obs z = y} reachable) w).toReal =
        fiberWeight P obs y w / signalMass P obs y := by
    intro w
    calc
      ((P.filter {z | obs z = y} reachable) w).toReal =
          (({z | obs z = y}.indicator (fun z => P z)) w *
            (в€‘' z, ({v | obs v = y}.indicator (fun v => P v)) z)вЃ»В№).toReal := by
        exact congrArg (fun value : ENNReal => value.toReal)
          (PMF.filter_apply (p := P) (s := {z | obs z = y}) reachable w)
      _ = (({z | obs z = y}.indicator (fun z => P z)) w).toReal *
          (signalMass P obs y)вЃ»В№ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_inv, tsum_fintype, fiber_sum_toReal]
      _ = fiberWeight P obs y w / signalMass P obs y := by
        by_cases same : obs w = y <;>
          simp [Set.indicator, fiberWeight, same, div_eq_mul_inv]
  calc
    conditionalScore P obs utility a y =
        expect (P.filter {w | obs w = y} reachable) (utility a) := by
      simp only [conditionalScore, conditionalLaw, dif_pos reachable]
    _ = в€‘ w, (fiberWeight P obs y w * utility a w) / signalMass P obs y := by
      rw [expect_eq_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [point]
      ring
    _ = (в€‘ w, fiberWeight P obs y w * utility a w) / signalMass P obs y := by
      simp only [Finset.sum_div]

private theorem weighted_conditional_score (P : PMF О©) (obs : О© в†’ Y)
    (utility : A в†’ О© в†’ в„ќ) (a : A) (y : Y) :
    signalMass P obs y * conditionalScore P obs utility a y =
      в€‘ w, fiberWeight P obs y w * utility a w := by
  by_cases zero : signalMass P obs y = 0
  В· have weightsZero : в€Ђ w, fiberWeight P obs y w = 0 := by
      have allZero := (Finset.sum_eq_zero_iff_of_nonneg
        (fun w (_ : w в€€ (Finset.univ : Finset О©)) => fiberWeight_nonneg P obs y w)).mp zero
      intro w
      exact allZero w (Finset.mem_univ w)
    simp [zero, weightsZerЧB€0­И]™HЬЪ]]™H€ЪYЫ[X\ЬИШњИHЏHћB€Ш\Щ\ИЫЬ—Щ\WЫЩ—ЫH
ЪYЫ[X\ЬЧЫ›Ы›™YИШњИJHЪ]€0­И^XЭ€0­И^XЭ[ЩK™[[H
™\›ИњЮ[[JB€ќИШЫЫ™][Ы[ЬШЫЬ™WЩњXЭ[Ы€ШњИ][]HHHЬЪ]]™WB€љY[ЬЪ[\Ю™\›ЭП€љ[™В‚™Y€ЫXЮTШЫЬ™H
€Q€3ЄJH
ШњИ€3ЄH8Ў¤€JH
][]H€H8Ў¤€3ЄH8Ў¤€8Ў'JB€
ЫXЮH€H8Ў¤€JH€8Ў'HЏB€^XЭ
ќ[€ИO€][]H
ЫXЮH
ШњИКJHКB‚њљ]]H[Ь™[HЫXЮWЬШЫЬ™WЭЭЩ\€
€Q€3ЄJH
ШњИ€3ЄH8Ў¤€JB€
][]H€H8Ў¤€3ЄH8Ў¤€8Ў'JH
ЫXЮH€H8Ў¤€JH‚€ЫXЮTШЫЬ™HШњИ][]HЫXЮHB€8ў$HKЪYЫ[X\ЬИШњИH
€ЫЫ™][Ы[ШЫЬ™HШњИ][]H
ЫXЮHJHHЏHћB€Ш[В€ЫXЮTШЫЬ™HШњИ][]HЫXЮHB€8ў$HЛ8ў$HKY€ШњИИHH[€
КKќФ™X[
€][]H
ЫXЮHJHИ[ЩHЏHћB€ќИЬЫXЮTШЫЬ™K^XЭЩ\WЬЭ[WB€\Hљ[њЩ]њЭ[WШЫЫ™Ь€™›€[ќ›ИИВ€Ъ[\€ИH8ў$HK8ў$HЛY€ШњИИHH[€
КKќФ™X[
€][]H
ЫXЮHJHИ[ЩHЏB€љ[њЩ]њЭ[WШЫЫ[B€ИH8ў$HK8ў$HЛљX™\•ЩZYЪШњИHИ
€][]H
ЫXЮHJHИЏHћB€Ъ[\ЩљX™\•ЩZYЪ]WЫ][B€ИH8ў$HKЪYЫ[X\ЬИШњИH
€ЫЫ™][Ы[ШЫЬ™HШњИ][]H
ЫXЮHJHHЏHћB€\Hљ[њЩ]њЭ[WШЫЫ™Ь€™›€[ќ›ИHВ€^XЭ
ЩZYЪYШЫЫ™][Ы[ЬШЫЬ™HШњИ][]H
ЫXЮHJHJKњЮ[[B‚њљ]]H[Ь™[Hљ[љ]WЩ^XЭЫ[Ы›И
€Q€3ЄJH
€И€3ЄH8Ў¤€8Ў'JB€
›Э[™€8ў Л€И8ўiИКH€^XЭ€8ўi^XЭИЏHћB€ќИЩ^XЭЩ\WЬЭ[K^XЭЩ\WЬЭ[WB€^XЭљ[њЩ]њЭ[WЫWЬЭ[H
ќ[€ИИO‚€][ЫWЫ][ЫЩ—Ы›Ы›™YЧЫYќ
›Э[™КHS“”™X[ќФ™X[Ы›Ы›™YКB‚њљ]]HY€Ь™YYPXЭ[Ы€
И€љ[њЩ]JH
И€Л“›Ы™[\JH
ШЫЬ™H€H8Ў¤€8Ў'JH€HЏHћB€Ы\ЬЪXШ[€^XЭЫ\ЬЪXШ[ЪЫЬЩH
љ[њЩ]™^\ЭЧЫY[WЩ\WЬЭ\	ИИШЫЬ™JB‚њљ]]H[Ь™[HЬ™YYPXЭ[Ы—ЬЬXИ
И€љ[њЩ]JH
И€Л“›Ы™[\JH
ШЫЬ™H€H8Ў¤€8Ў'JH‚€Ь™YYPXЭ[Ы€ИИШЫЬ™H8ў"И8ў)ИЛњЭ\	ИИШЫЬ™HHШЫЬ™H
Ь™YYPXЭ[Ы€ИИШЫЬ™JHЏHћB€Ы\ЬЪXШ[€^XЭЫ\ЬЪXШ[ЪЫЬЩWЬЬXИ
љ[њЩ]™^\ЭЧЫY[WЩ\WЬЭ\	ИИШЫЬ™JB‚њљ]]H[Ь™[HШЫЬ™WЫWШЫЫ™][Ы[ЫX^
€Q€3ЄJH
ШњИ€3ЄH8Ў¤€JB€
][]H€H8Ў¤€3ЄH8Ў¤€8Ў'JH
И€љ[њЩ]JH
И€Л“›Ы™[\JB€
ЫXЮH€H8Ў¤€JH
™X\ЪX›H€8ў KЫXЮHH8ў"КH‚€ЫXЮTШЫЬ™HШњИ][]HЫXЮH8ўi€^XЭ
ЪYЫ[]ИШњКB€
ќ[€HO€ЛњЭ\	ИИ
ќ[€HO€ЫЫ™][Ы[ШЫЬ™HШњИ][]HHJJHЏHћB€ќИЬЫXЮWЬШЫЬ™WЭЭЩ\‹ЪYЫ[Щ^XЭЩ\WЬЭ[WB€\Hљ[њЩ]њЭ[WЫWЬЭ[B€[ќ›ИHВ€^XЭ][ЫWЫ][ЫЩ—Ы›Ы›™YЧЫYќ€
љ[њЩ]›WЬЭ\	И
ќ[€HO€ЫЫ™][Ы[ШЫЬ™HШњИ][]HHJH
™X\ЪX›HJJB€
ЪYЫ[X\ЬЧЫ›Ы›™YИШњИJB‚‹ЛKHЬљYЪ[[‹ЌЭ™\€\љ]\ћHљ[љ]H™X[›ШXљ[]Y\И[™™X[][]Y\Л‚•HШ[YH›Ы™[\Hљ[љ]HYШ[XЭ[Ы€Щ]\И]Z[X›HYќ\€]™\ћHЪYЫ[В[Л][YYЪYЫ[Э]YЪY\И\™H™X\ЪX›H[€\ИЫ™KYXЪ\Ъ[Ы€[Щ[€KВќ[Ь™[Hљ[љ]WШЫЫ™][Ы[Э[YWЫЩ—Ъ[™›Ь›X][Ы‚€
€Q€3ЄJH
ШњИ€3ЄH8Ў¤€JH
][]H€H8Ў¤€3ЄH8Ў¤€8Ў'JH
ЧпUH
H
И€Л“›Ы™[\JH‚€ЛњЭ\	ИИ
ќ[€HO€^XЭ
][]HJJH8ўi€^XЭ
ЪYЫ[]ИШњКB€
ќ[€HO€ЛњЭ\	ИИ
ќ[€HO€ЫЫ™][Ы[ШЫЬ™HШњИ][]HHJJH8ў)В€^XЭ
ЪYЫ[]ИШњКB€
ќ[€HO€ЛњЭ\	ИИ
ќ[€HO€ЫЫ™][Ы[ШЫЬ™HШњИ][]HHJJH8ўi€^XЭ
ќ[€ИO€ЛњЭ\	ИИ
ќ[€HO€][]HHКJHЏHћB€Ы\ЬЪXШ[€ЫЫњЭќXЭЬ‚€0­И\Hљ[њЩ]њЭ\	ЧЫHИ
ќ[€HO€^XЭ
][]HJJB€[ќ›ИHY[X™\‚€^XЭШЫЬ™WЫWШЫЫ™][Ы[ЫX^ШњИ][]HИИ
ќ[€ИO€JH
ќ[€ИO€Y[X™\ЉB€0­И]Ь™YYH€H8Ў¤€HЏHќ[€HO‚€Ь™YYPXЭ[Ы€ИИ
ќ[€HO€ЫЫ™][Ы[ШЫЬ™HШњИ][]HHJB€]™HЬ™YYU[YH‚€ЫXЮTШЫЬ™HШњИ][]HЬ™YYHB€^XЭ
ЪYЫ[]ИШњКB€
ќ[€HO€ЛњЭ\	ИИ
ќ[€HO€ЫЫ™][Ы[ШЫЬ™HШњИ][]HHJJHЏHћB€ќИЬЫXЮWЬШЫЬ™WЭЭЩ\‹ЪYЫ[Щ^XЭЩ\WЬЭ[WB€\Hљ[њЩ]њЭ[WШЫЫ™Ь€™›€[ќ›ИHВ€^XЭЫЫ™Ьђ\™И
ќ[€[YHO€ЪYЫ[X\ЬИШњИH
€[YJB€
Ь™YYPXЭ[Ы—ЬЬXИИИ
ќ[€HO€ЫЫ™][Ы[ШЫЬ™HШњИ][]HHJJKЊ‹њЮ[[B€ќИшЎ¤Ь™YYU[YWB€\Hљ[љ]WЩ^XЭЫ[Ы›В€[ќ›ИВ€^XЭљ[њЩ]›WЬЭ\	И
ќ[€HO€][]HHКB€
Ь™YYPXЭ[Ы—ЬЬXИИВ€
ќ[€HO€ЫЫ™][Ы[ШЫЬ™HШњИ][]HH
ШњИКJJKЊB‚‹ЛKHЬљYЪ[[‹Ќ›Шќ\ЭЫ]\ЩN€HШ[YHљ[љ]HYШ[њ[Ъ\И\™H™]Z[™Y[™]™\ћHЫXЭ[Ы€[X™YИ\ИH™X\ЪX›HЫXЮHYЫ›Ьљ[™ИHЪYЫ[‚“Ы›HXXЪњ[Ъ	ЬИXЭX[Q€\И\ЩYИYШ[њ[Ъ\И™XЩZ]™H›Иљ[Ь‹€KВќ[Ь™[Hљ[љ]WЬ›Шќ\ЭЪ[™›Ь›X][Ы—Ы[Ы›ЭЫ™B€Т€€\_H
њ[Ъ\И€љ[њЩ]ЉH
€€њ[Ъ\Л“›Ы™[\JB€
€€8Ў¤€Q€3ЄJH
ШњИ€€8Ў¤€3ЄH8Ў¤€JB€
][]H€€8Ў¤€H8Ў¤€3ЄH8Ў¤€8Ў'JB€
И€љ[њЩ]JH
И€Л“›Ы™[\JH
ЫXЪY\И€љ[њЩ]
H8Ў¤€JJB€
YЫ›Ь™H€8ў H8ў"Л
ќ[€И€HO€JH8ў"ЫXЪY\КH‚€ЛњЭ\	ИИ
ќ[€HO€њ[Ъ\Лљ[™‰И‚€
ќ[€€O€^XЭ
ЉH
][]H€JJJH8ўi€ЫXЪY\ЛњЭ\	И
ћB€ШќZ[€8§кKx§кHЏHВ€^XЭ8§к
ќ[€ИO€JKYЫ›Ь™HHx§кJB€
ќ[€ЫXЮHO€њ[Ъ\Лљ[™‰И‚€
ќ[€€O€ЫXЮTШЫЬ™H
ЉH
ШњИЉH
][]HЉHЫXЮJJHЏHћB€Ы\ЬЪXШ[€\Hљ[њЩ]њЭ\	ЧЫHВ€
ќ[€HO€њ[Ъ\Лљ[™‰И€
ќ[€€O€^XЭ
ЉH
][]H€JJJB€[ќ›ИHY[X™\‚€Ъ[\HЫ›HЬЫXЮTШЫЬ™WH\Ъ[™В€
љ[њЩ]›WЬЭ\	В€
ќ[€ЫXЮHO€њ[Ъ\Лљ[™‰И‚€
ќ[€€O€ЫXЮTШЫЬ™H
ЉH
ШњИЉH
][]HЉHЫXЮJJB€
YЫ›Ь™HHY[X™\ЉJB‚™[™ќ\љ\УX[‹ђШ[™Y]\Л•L—НЫЫ™][Ы[[™›Ь›X][ЫЊЊЌЊLМB