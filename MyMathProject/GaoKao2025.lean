/-
2025 年高考新课标 I 卷数学第 19 题

用 Mathlib 做严格证明：导数、特殊值、单调性与最值都由库引理核验。

(1) 求 f(x) = 5 cos x − cos 5x 在 [0, π/4] 上的最大值；
(2) 给定 θ ∈ (0, π) 与 a ∈ ℝ，证明存在 y ∈ [a−θ, a+θ] 使得 cos y ≤ cos θ；
(3) 若存在 φ ∈ ℝ 使 5 cos x − cos(5x+φ) ≤ b 对一切实数 x 成立，求 b 的最小值。
-/

import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

namespace MyMathProject.GaoKao2025

open Real Set Polynomial.Chebyshev

noncomputable section

def f (x : ℝ) : ℝ := 5 * cos x - cos (5 * x)

def g (φ x : ℝ) : ℝ := 5 * cos x - cos (5 * x + φ)

/-! ## 预备：导数与倍角 -/

lemma hasDerivAt_f (x : ℝ) :
    HasDerivAt f (5 * (sin (5 * x) - sin x)) x := by
  have h1 : HasDerivAt (fun t => 5 * cos t) (5 * (-sin x)) x :=
    (hasDerivAt_cos x).const_mul 5
  have h5 : HasDerivAt (fun t : ℝ => 5 * t) 5 x := by
    simpa using (hasDerivAt_id x).const_mul (5 : ℝ)
  have h2 : HasDerivAt (fun t => cos (5 * t)) ((-sin (5 * x)) * 5) x :=
    (hasDerivAt_cos (5 * x)).comp x h5
  unfold f
  convert h1.sub h2 using 1
  ring

lemma deriv_f (x : ℝ) : deriv f x = 5 * (sin (5 * x) - sin x) :=
  (hasDerivAt_f x).deriv

lemma differentiable_f : Differentiable ℝ f :=
  fun x => (hasDerivAt_f x).differentiableAt

lemma continuous_f : Continuous f :=
  differentiable_f.continuous

lemma sin_five_sub_sin (x : ℝ) :
    sin (5 * x) - sin x = 2 * sin (2 * x) * cos (3 * x) := by
  have h := sin_sub_sin (5 * x) x
  have h1 : ((5 * x - x) / 2) = 2 * x := by ring
  have h2 : ((5 * x + x) / 2) = 3 * x := by ring
  simpa [h1, h2] using h

lemma deriv_f_trig (x : ℝ) :
    deriv f x = 10 * sin (2 * x) * cos (3 * x) := by
  rw [deriv_f, sin_five_sub_sin]
  ring

lemma pi_div_six_lt_pi_div_four : π / 6 < π / 4 := by
  have : (0 : ℝ) < π := pi_pos
  rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
  linarith

lemma pi_div_six_mem : π / 6 ∈ Icc (0 : ℝ) (π / 4) :=
  ⟨div_nonneg pi_pos.le (by norm_num), pi_div_six_lt_pi_div_four.le⟩

/-! ## 第 (1) 问：驻点处求导并比较 -/

lemma f_pi_div_six : f (π / 6) = 3 * √3 := by
  have hx : (5 : ℝ) * (π / 6) = 5 * π / 6 := by ring
  have hcs : cos (5 * π / 6) = -cos (π / 6) := by
    have : 5 * π / 6 = π - π / 6 := by ring
    rw [this, cos_pi_sub]
  simp only [f, hx, hcs, cos_pi_div_six]
  ring

lemma deriv_f_nonneg_left {x : ℝ} (hx : x ∈ Ioo 0 (π / 6)) : 0 ≤ deriv f x := by
  rw [deriv_f_trig]
  have hx0 : 0 < x := hx.1
  have hx1 : x < π / 6 := hx.2
  have hsin : 0 < sin (2 * x) := by
    apply sin_pos_of_mem_Ioo
    constructor
    · nlinarith
    · nlinarith [pi_pos]
  have hcos : 0 < cos (3 * x) := by
    apply cos_pos_of_mem_Ioo
    constructor
    · nlinarith [pi_pos]
    · nlinarith
  nlinarith

lemma deriv_f_nonpos_right {x : ℝ} (hx : x ∈ Ioo (π / 6) (π / 4)) : deriv f x ≤ 0 := by
  rw [deriv_f_trig]
  have hx0 : π / 6 < x := hx.1
  have hx1 : x < π / 4 := hx.2
  have hsin : 0 < sin (2 * x) := by
    apply sin_pos_of_mem_Ioo
    constructor
    · nlinarith [pi_pos]
    · nlinarith [pi_pos]
  have hcos : cos (3 * x) < 0 := by
    apply cos_neg_of_pi_div_two_lt_of_lt
    · nlinarith
    · nlinarith [pi_pos]
  nlinarith

/-- 在 `[0, π/4]` 上，`f` 于 `π/6` 取到最大值 `3√3`。 -/
theorem part1 : IsMaxOn f (Icc 0 (π / 4)) (π / 6) ∧ f (π / 6) = 3 * √3 := by
  refine ⟨?_, f_pi_div_six⟩
  have hf := continuous_f
  exact isMaxOn_Icc_of_deriv
    hf.continuousAt hf.continuousAt hf.continuousAt
    differentiable_f.differentiableOn differentiable_f.differentiableOn
    (fun _ hx => deriv_f_nonneg_left hx) (fun _ hx => deriv_f_nonpos_right hx)

/-! ## 全局表达式：切比雪夫多项式给出 `f` 的代数形式 -/

lemma eval_T_two (t : ℝ) : (T ℝ 2).eval t = 2 * t ^ 2 - 1 := by
  simp [T_two]

lemma eval_T_three (t : ℝ) : (T ℝ 3).eval t = 4 * t ^ 3 - 3 * t := by
  have h : (3 : ℤ) = (1 : ℤ) + 2 := by decide
  rw [h, T_add_two]
  simp [T_one, eval_T_two]
  ring

lemma eval_T_four (t : ℝ) : (T ℝ 4).eval t = 8 * t ^ 4 - 8 * t ^ 2 + 1 := by
  have h : (4 : ℤ) = (2 : ℤ) + 2 := by decide
  rw [h, T_add_two]
  simp [eval_T_two, eval_T_three]
  ring

lemma eval_T_five (t : ℝ) : (T ℝ 5).eval t = 16 * t ^ 5 - 20 * t ^ 3 + 5 * t := by
  have h : (5 : ℤ) = (3 : ℤ) + 2 := by decide
  rw [h, T_add_two]
  simp [eval_T_three, eval_T_four]
  ring

lemma f_as_poly (x : ℝ) : f x = 20 * cos x ^ 3 - 16 * cos x ^ 5 := by
  have hc : cos (5 * x) = (T ℝ 5).eval (cos x) := by
    simp [T_real_cos]
  rw [f, hc, eval_T_five]
  ring

def h (t : ℝ) : ℝ := 20 * t ^ 3 - 16 * t ^ 5

lemma f_eq_h_cos (x : ℝ) : f x = h (cos x) :=
  f_as_poly x

lemma hasDerivAt_h (t : ℝ) :
    HasDerivAt h (60 * t ^ 2 - 80 * t ^ 4) t := by
  have h3 := (hasDerivAt_pow 3 t).const_mul (20 : ℝ)
  have h5 := (hasDerivAt_pow 5 t).const_mul (16 : ℝ)
  have hf := h3.sub h5
  convert hf using 1
  · ext; simp [h]
  · ring

lemma deriv_h (t : ℝ) : deriv h t = 20 * t ^ 2 * (3 - 4 * t ^ 2) := by
  have := (hasDerivAt_h t).deriv
  convert this using 1
  ring

lemma differentiable_h : Differentiable ℝ h :=
  fun t => (hasDerivAt_h t).differentiableAt

lemma continuous_h : Continuous h :=
  differentiable_h.continuous

lemma sqrt3_div_two_lt_one : √3 / 2 < 1 := by
  rw [div_lt_one (by norm_num)]
  refine (Real.sqrt_lt' (by norm_num)).2 ?_
  norm_num

lemma deriv_h_nonneg_left {t : ℝ} (ht : t ∈ Ioo 0 (√3 / 2)) : 0 ≤ deriv h t := by
  rw [deriv_h]
  have ht0 : 0 < t := ht.1
  have ht1 : t < √3 / 2 := ht.2
  have hsq : t ^ 2 < 3 / 4 := by
    have := sq_lt_sq₀ ht0.le (by positivity)
    have hbound : (√3 / 2) ^ 2 = 3 / 4 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    nlinarith
  have : 0 ≤ 3 - 4 * t ^ 2 := by nlinarith
  positivity

lemma deriv_h_nonpos_right {t : ℝ} (ht : t ∈ Ioo (√3 / 2) 1) : deriv h t ≤ 0 := by
  rw [deriv_h]
  have ht0 : √3 / 2 < t := ht.1
  have ht1 : t < 1 := ht.2
  have hsq : 3 / 4 < t ^ 2 := by
    have hbound : (√3 / 2) ^ 2 = 3 / 4 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    have hcmp : (√3 / 2) ^ 2 < t ^ 2 :=
      (sq_lt_sq₀ (by positivity : (0 : ℝ) ≤ √3 / 2)
        (le_trans (by positivity : (0 : ℝ) ≤ √3 / 2) ht0.le)).2 ht0
    nlinarith
  have h1 : 0 ≤ t ^ 2 := sq_nonneg t
  have h2 : 3 - 4 * t ^ 2 ≤ 0 := by nlinarith
  nlinarith

lemma h_sqrt3_div_two : h (√3 / 2) = 3 * √3 := by
  have hs : (√3 / 2) ^ 2 = 3 / 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h3 : (√3 / 2) ^ 3 = √3 ^ 3 / 8 := by
    rw [div_pow]; norm_num
  have h3' : √3 ^ 3 = 3 * √3 := by
    have : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [pow_succ, this]
  have h5 : (√3 / 2) ^ 5 = (√3 / 2) ^ 3 * (√3 / 2) ^ 2 := by ring
  simp only [h, h5, h3, hs, h3']
  ring

lemma h_max_on_unit : IsMaxOn h (Icc 0 1) (√3 / 2) := by
  have hh := continuous_h
  have mem : √3 / 2 ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (Real.sqrt_nonneg _) (by norm_num), sqrt3_div_two_lt_one.le⟩
  exact isMaxOn_Icc_of_deriv
    hh.continuousAt hh.continuousAt hh.continuousAt
    differentiable_h.differentiableOn differentiable_h.differentiableOn
    (fun _ ht => deriv_h_nonneg_left ht) (fun _ ht => deriv_h_nonpos_right ht)

lemma h_nonneg_on_Icc_zero_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ h t := by
  have h0 : h 0 = 0 := by simp [h]
  have h1 : h 1 = 4 := by simp [h]; ring
  by_cases hle : t ≤ √3 / 2
  · have mono : MonotoneOn h (Icc (0 : ℝ) (√3 / 2)) :=
      monotoneOn_of_deriv_nonneg (convex_Icc 0 (√3 / 2)) continuous_h.continuousOn
        (by
          rw [interior_Icc]
          exact differentiable_h.differentiableOn)
        (fun x hx => by
          rw [interior_Icc] at hx
          exact deriv_h_nonneg_left hx)
    have : h 0 ≤ h t :=
      mono ⟨le_rfl, by positivity⟩ ⟨ht.1, hle⟩ ht.1
    linarith
  · have anti : AntitoneOn h (Icc (√3 / 2) 1) :=
      antitoneOn_of_deriv_nonpos (convex_Icc (√3 / 2) 1) continuous_h.continuousOn
        (by
          rw [interior_Icc]
          exact differentiable_h.differentiableOn)
        (fun x hx => by
          rw [interior_Icc] at hx
          exact deriv_h_nonpos_right hx)
    have : h 1 ≤ h t :=
      anti ⟨le_of_not_ge hle, ht.2⟩ ⟨sqrt3_div_two_lt_one.le, le_rfl⟩ ht.2
    linarith

lemma h_le_three_sqrt3 {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : h t ≤ 3 * √3 := by
  by_cases ht0 : 0 ≤ t
  · have hle : h t ≤ h (√3 / 2) := h_max_on_unit ⟨ht0, ht.2⟩
    linarith [h_sqrt3_div_two]
  · have htneg : t < 0 := lt_of_not_ge ht0
    have hodd : h t = -h (-t) := by simp [h]; ring
    have hnn : 0 ≤ h (-t) :=
      h_nonneg_on_Icc_zero_one ⟨neg_nonneg.mpr htneg.le, by linarith [ht.1]⟩
    have : h t ≤ 0 := by linarith
    linarith [Real.sqrt_nonneg (3 : ℝ)]

lemma f_global_ub (x : ℝ) : f x ≤ 3 * √3 := by
  rw [f_eq_h_cos]
  exact h_le_three_sqrt3 ⟨neg_one_le_cos x, cos_le_one x⟩

/-! ## 第 (2) 问

坏点 `cos y > cos θ` 在一个周期 `(-π, π]` 内恰好是开区间 `(-θ, θ)`。
周期延拓后，坏点是一串开区间 `(2kπ - θ, 2kπ + θ)`，每段长度 `2θ`。
题目给的 `[a - θ, a + θ]` 是同长度的闭区间：中心若已是好点就取中心；
中心若落在坏开区间内，闭区间一定盖住边界 `±θ`，取边界即可。
（这就是“长 `2θ` 的闭区间塞不进长 `2θ` 的开区间”。）
-/

lemma reduce_mod_two_pi (a : ℝ) :
    toIocMod two_pi_pos (-π) a ∈ Ioc (-π) π ∧
      cos (toIocMod two_pi_pos (-π) a) = cos a ∧
      toIocMod two_pi_pos (-π) a + toIocDiv two_pi_pos (-π) a * (2 * π) = a := by
  refine ⟨?_, ?_, ?_⟩
  · have := toIocMod_mem_Ioc two_pi_pos (-π) a
    simpa [neg_add_cancel, two_mul, add_comm] using this
  · let a' := toIocMod two_pi_pos (-π) a
    let n := toIocDiv two_pi_pos (-π) a
    have hsum := toIocMod_add_toIocDiv_mul two_pi_pos (-π) a
    calc
      cos a' = cos (a' + n * (2 * π)) := (cos_add_int_mul_two_pi a' n).symm
      _ = cos a := by rw [hsum]
  · exact toIocMod_add_toIocDiv_mul two_pi_pos (-π) a

/-- 在 `(-π, π]` 内，坏点 `cos y > cos θ` 恰好是 `(-θ, θ)`。 -/
lemma cos_gt_cos_theta_iff {θ y : ℝ} (hθ0 : 0 < θ) (hθπ : θ < π)
    (hy : y ∈ Ioc (-π) π) :
    cos θ < cos y ↔ y ∈ Ioo (-θ) θ := by
  constructor
  · intro h
    by_cases hy0 : 0 ≤ y
    · have ylt : y < θ := by
        by_contra hge
        have := cos_le_cos_of_nonneg_of_le_pi hθ0.le hy.2 (le_of_not_gt hge)
        linarith
      exact ⟨by linarith, ylt⟩
    · have hzπ : -y ≤ π := by linarith [hy.1]
      have ygt : -θ < y := by
        by_contra hle
        have := cos_le_cos_of_nonneg_of_le_pi hθ0.le hzπ (by linarith)
        rw [cos_neg] at this
        linarith
      exact ⟨ygt, by linarith [hy0]⟩
  · intro hyo
    have := cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg y) hθπ.le (abs_lt.mpr hyo)
    rwa [cos_abs] at this

lemma part2_on_rep (θ a : ℝ) (hθ0 : 0 < θ) (hθπ : θ < π)
    (ha : a ∈ Ioc (-π) π) :
    ∃ y ∈ Icc (a - θ) (a + θ), cos y ≤ cos θ := by
  by_cases hbad : a ∈ Ioo (-θ) θ
  · -- 中心落在坏开区间内：同长闭区间必盖住边界。
    by_cases hpos : 0 ≤ a
    · refine ⟨θ, ⟨by linarith [hbad.2], by linarith [hpos]⟩, le_rfl⟩
    · refine ⟨-θ, ⟨by linarith [hpos], by linarith [hbad.1]⟩, ?_⟩
      simp [cos_neg]
  · -- 中心已是好点，直接取中心。
    refine ⟨a, ⟨by linarith [hθ0], by linarith [hθ0]⟩, ?_⟩
    exact le_of_not_gt ((cos_gt_cos_theta_iff hθ0 hθπ ha).not.mpr hbad)

theorem part2 (θ a : ℝ) (hθ0 : 0 < θ) (hθπ : θ < π) :
    ∃ y ∈ Icc (a - θ) (a + θ), cos y ≤ cos θ := by
  obtain ⟨ha', _, hsum⟩ := reduce_mod_two_pi a
  obtain ⟨y', hy', hcy⟩ := part2_on_rep θ _ hθ0 hθπ ha'
  let n := toIocDiv two_pi_pos (-π) a
  refine ⟨y' + n * (2 * π), ?_, ?_⟩
  · have : a = toIocMod two_pi_pos (-π) a + n * (2 * π) := hsum.symm
    rw [this]
    exact ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
  · simpa [cos_add_int_mul_two_pi] using hcy

/-! ## 第 (3) 问

任取 `φ`。限制 `x ∈ [-t, t]`，则 `5 cos x ≥ 5 cos t`。
此时 `y = 5x + φ` 遍历 `[φ - 5t, φ + 5t]`，由第 (2) 问存在 `y` 使 `cos y ≤ cos 5t`。
取 `x = (y - φ) / 5`，则 `g(x) ≥ 5 cos t - cos 5t = f(t)`。
取 `t = π/6` 得每个 `φ` 都有某个 `x` 使 `g ≥ 3√3`。
`φ = 0` 时 `g = f ≤ 3√3`（全局上界来自切比雪夫），故最小 `b` 为 `3√3`。
-/

lemma g_zero (x : ℝ) : g 0 x = f x := by
  simp [g, f]

/-- `|x| ≤ t ≤ π` 时，`cos` 在 `[0, π]` 递减且为偶函数，故 `cos t ≤ cos x`。 -/
lemma cos_le_cos_of_abs_le {x t : ℝ} (htπ : t ≤ π) (hx : |x| ≤ t) :
    cos t ≤ cos x := by
  have := cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) htπ hx
  rwa [cos_abs] at this

lemma part3_lower (φ : ℝ) : ∃ x, 3 * √3 ≤ g φ x := by
  set t : ℝ := π / 6 with ht
  set θ : ℝ := 5 * t with hθ
  have ht0 : 0 < t := by rw [ht]; exact div_pos pi_pos (by norm_num)
  have htπ : t ≤ π := by rw [ht]; nlinarith [pi_pos]
  have hθ0 : 0 < θ := mul_pos (by norm_num) ht0
  have hθπ : θ < π := by rw [hθ, ht]; nlinarith [pi_pos]
  obtain ⟨y, hy, hcy⟩ := part2 θ φ hθ0 hθπ
  let x := (y - φ) / 5
  have hyx : 5 * x + φ = y :=
    calc
      5 * ((y - φ) / 5) + φ = y - φ + φ := by
        rw [mul_div_cancel₀ _ (by norm_num : (5 : ℝ) ≠ 0)]
      _ = y := by ring
  have hx : |x| ≤ t := by
    have hyφ : |y - φ| ≤ θ := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hxabs : |x| = |y - φ| / 5 := by
      simp [x, abs_div]
    have : |x| ≤ θ / 5 := by
      rw [hxabs]
      exact div_le_div_of_nonneg_right hyφ (by norm_num)
    have hθ5 : θ / 5 = t := by rw [hθ]; field_simp
    rwa [hθ5] at this
  have hcosx : cos t ≤ cos x := cos_le_cos_of_abs_le htπ hx
  refine ⟨x, ?_⟩
  have hg : g φ x = 5 * cos x - cos y := by
    simp only [g, hyx]
  have hft : f t ≤ g φ x := by
    have : 5 * cos t ≤ 5 * cos x :=
      mul_le_mul_of_nonneg_left hcosx (by norm_num)
    simp only [f, hg]
    linarith [hcy]
  have : f t = 3 * √3 := f_pi_div_six
  linarith

lemma part3_phi_zero : ∀ x, g 0 x ≤ 3 * √3 := by
  intro x
  rw [g_zero]
  exact f_global_ub x

/-- 合格上界 `b` 的最小值是 `3√3`。 -/
theorem part3 : IsLeast {b : ℝ | ∃ φ, ∀ x, g φ x ≤ b} (3 * √3) := by
  constructor
  · exact ⟨0, part3_phi_zero⟩
  · intro b hb
    obtain ⟨φ, hφ⟩ := hb
    obtain ⟨x, hx⟩ := part3_lower φ
    exact hx.trans (hφ x)

end

end MyMathProject.GaoKao2025
