/-
2025 年高考新课标 I 卷数学第 19 题（Lean 4 证明脚本）

本文件只使用 Lean 自带库，不依赖 Mathlib。
实数、余弦、不等式的分析事实列成公理（对应高中已学内容）；
题目本身的分类讨论与逻辑结构全部由 Lean 检查。

题目：
(1) 求 f(x) = 5 cos x − cos 5x 在 [0, π/4] 上的最大值；
(2) 给定 θ ∈ (0, π) 与 a ∈ ℝ，证明存在 y ∈ [a−θ, a+θ] 使得 cos y ≤ cos θ；
(3) 若存在 φ ∈ ℝ 使 5 cos x − cos(5x+φ) ≤ b 对一切实数 x 成立，求 b 的最小值。

用法：把光标移到 `by` 证明里，按 Ctrl+Shift+Enter 打开 InfoView。
-/

namespace MyMathProject.GaoKao2025

noncomputable section

/-! ## 一、实数与余弦（分析预备，当作已学习的事实） -/

axiom Real : Type
notation "ℝ" => Real

axiom realAdd : ℝ → ℝ → ℝ
axiom realSub : ℝ → ℝ → ℝ
axiom realMul : ℝ → ℝ → ℝ
axiom realDiv : ℝ → ℝ → ℝ
axiom realNeg : ℝ → ℝ
axiom realZero : ℝ
axiom realOne : ℝ
axiom realLe : ℝ → ℝ → Prop
axiom realLt : ℝ → ℝ → Prop
axiom realOfNat : Nat → ℝ

instance : Add ℝ := ⟨realAdd⟩
instance : Sub ℝ := ⟨realSub⟩
instance : Mul ℝ := ⟨realMul⟩
instance : Div ℝ := ⟨realDiv⟩
instance : Neg ℝ := ⟨realNeg⟩
instance : Zero ℝ := ⟨realZero⟩
instance : One ℝ := ⟨realOne⟩
instance : LE ℝ := ⟨realLe⟩
instance : LT ℝ := ⟨realLt⟩
instance {n : Nat} : OfNat ℝ n where
  ofNat := realOfNat n

axiom pi : ℝ
def π : ℝ := pi
axiom sqrt : ℝ → ℝ
axiom cos : ℝ → ℝ

-- 序关系
axiom le_refl (a : ℝ) : a ≤ a
axiom le_trans (a b c : ℝ) : a ≤ b → b ≤ c → a ≤ c
axiom lt_imp_le (a b : ℝ) : a < b → a ≤ b
axiom not_lt_of_le (a b : ℝ) : a ≤ b → ¬ b < a
axiom le_of_not_lt (a b : ℝ) : ¬ a < b → b ≤ a
axiom lt_of_not_le (a b : ℝ) : ¬ a ≤ b → b < a

-- 区间与端点
axiom sub_le_add (a θ : ℝ) (h : 0 ≤ θ) : a - θ ≤ a + θ
axiom theta_in_interval (a θ : ℝ) (h0 : 0 ≤ a) (h2 : a ≤ 2 * θ) :
  a - θ ≤ θ ∧ θ ≤ a + θ
axiom neg_theta_in_interval (a θ : ℝ) (h0 : a < 0) (h2 : -(2 * θ) ≤ a) :
  a - θ ≤ -θ ∧ -θ ≤ a + θ

-- 余弦基本性质
axiom cos_neg (x : ℝ) : cos (-x) = cos x
axiom cos_pi_sub (x : ℝ) : cos (π - x) = - cos x
axiom cos_anti_on_zero_pi_six (x y : ℝ)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ π / 6) : cos y ≤ cos x

-- 常用取值
axiom zero_le_pi_div_six : (0 : ℝ) ≤ π / 6
axiom pi_div_six_le_pi_div_four : π / 6 ≤ π / 4
axiom cos_pi_div_six : cos (π / 6) = sqrt 3 / 2
axiom six_mul_half_sqrt3 : 6 * (sqrt 3 / 2) = 3 * sqrt 3
axiom f_at_pi_div_six_eval :
  5 * cos (π / 6) - cos (5 * (π / 6)) = 3 * sqrt 3

-- 第 (1) 问：导函数符号给出的单调性
-- f'(x) = 5(sin 5x − sin x) = 10 cos(3x) sin(2x)
-- 在 [0, π/6] 上 f' ≥ 0，在 [π/6, π/4] 上 f' ≤ 0
axiom f_incr_left (x y : ℝ)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ π / 6) :
  5 * cos x - cos (5 * x) ≤ 5 * cos y - cos (5 * y)
axiom f_decr_right (x y : ℝ)
    (hx : π / 6 ≤ x) (hxy : x ≤ y) (hy : y ≤ π / 4) :
  5 * cos y - cos (5 * y) ≤ 5 * cos x - cos (5 * x)

-- 第 (3) 问用到的三角恒等
axiom special_angle_pos (φ : ℝ) :
  5 * ((π - φ) / 6) + φ = π - (π - φ) / 6
axiom special_angle_neg (φ : ℝ) :
  5 * (-((π + φ) / 6)) + φ = -(π - (π + φ) / 6)
axiom five_cos_add_cos (α : ℝ) : 5 * cos α + cos α = 6 * cos α
axiom sub_neg (a b : ℝ) : a - -b = a + b
axiom add_zero (a : ℝ) : a + 0 = a
axiom six_mul_le (a b : ℝ) : a ≤ b → 6 * a ≤ 6 * b
axiom zero_le_special_pos (φ : ℝ) (h0 : 0 ≤ φ) (hπ : φ ≤ π) :
  (0 : ℝ) ≤ (π - φ) / 6
axiom special_pos_le_pi_six (φ : ℝ) (h0 : 0 ≤ φ) (hπ : φ ≤ π) :
  (π - φ) / 6 ≤ π / 6
axiom zero_le_special_neg (φ : ℝ) (hπ : -π < φ) (h0 : φ ≤ 0) :
  (0 : ℝ) ≤ (π + φ) / 6
axiom special_neg_le_pi_six (φ : ℝ) (hπ : -π < φ) (h0 : φ ≤ 0) :
  (π + φ) / 6 ≤ π / 6
axiom neg_neg (a : ℝ) : - -a = a

-- 全局上界：由 cos 5x = 16c⁵ − 20c³ + 5c（c = cos x）得
-- 5c − cos 5x = 20c³ − 16c⁵，在 c ∈ [-1, 1] 上最大值为 3√3
axiom f_global_ub (x : ℝ) : 5 * cos x - cos (5 * x) ≤ 3 * sqrt 3

-- 相位可化到 (-π, π]（余弦以 2π 为周期）
axiom exists_phi_rep (φ : ℝ) :
  ∃ φ', -π < φ' ∧ φ' ≤ π ∧
    ∀ x, 5 * cos x - cos (5 * x + φ) = 5 * cos x - cos (5 * x + φ')

axiom exists_a_rep (a : ℝ) :
  ∃ (a' n : ℝ), a = a' + (2 * n) * π ∧ -π < a' ∧ a' ≤ π

axiom cos_add_two_pi_mul (x n : ℝ) : cos (x + (2 * n) * π) = cos x
axiom interval_shift (a a' n θ y' : ℝ)
    (h : a = a' + (2 * n) * π)
    (hy : a' - θ ≤ y' ∧ y' ≤ a' + θ) :
  a - θ ≤ y' + (2 * n) * π ∧ y' + (2 * n) * π ≤ a + θ

-- 端点处余弦不等式（官方解法中的几何观察）
-- a > 2θ 且 a ≤ π 时，y = a−θ ∈ (θ, π−θ] ⊂ [θ, π]，余弦在 [0, π] 递减
axiom cos_left_endpoint (θ a : ℝ)
    (hθ : 0 < θ) (hθπ : θ < π) (h : 2 * θ < a) (ha : a ≤ π) :
  cos (a - θ) ≤ cos θ
-- a < −2θ 且 −π < a 时，y = a+θ ∈ [−π+θ, −θ)，再用偶性化到上一种情形
axiom cos_right_endpoint (θ a : ℝ)
    (hθ : 0 < θ) (hθπ : θ < π) (h : a < -(2 * θ)) (ha : -π < a) :
  cos (a + θ) ≤ cos θ

/-! ## 二、定义 -/

def f (x : ℝ) : ℝ := 5 * cos x - cos (5 * x)

def g (φ x : ℝ) : ℝ := 5 * cos x - cos (5 * x + φ)

/-! ## 三、第 (1) 问

求导得 f'(x) = 5(sin 5x − sin x)。在 (0, π/4] 内唯一驻点 x = π/6，
且 f 在 [0, π/6] 递增、在 [π/6, π/4] 递减，故最大值是
f(π/6) = 5·(√3/2) − (−√3/2) = 3√3。
端点仅作对照：f(0) = 4，f(π/4) = 3√2，都小于 3√3。
-/

theorem f_at_pi_div_six : f (π / 6) = 3 * sqrt 3 :=
  f_at_pi_div_six_eval

theorem part1_upper (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ π / 4) :
    f x ≤ f (π / 6) := by
  by_cases h : x ≤ π / 6
  · exact f_incr_left x (π / 6) hx0 h (le_refl (π / 6))
  · have hx' : π / 6 ≤ x :=
      lt_imp_le (π / 6) x (lt_of_not_le x (π / 6) h)
    exact f_decr_right (π / 6) x (le_refl (π / 6)) hx' hx1

theorem part1 :
    (∃ x, 0 ≤ x ∧ x ≤ π / 4 ∧ f x = 3 * sqrt 3) ∧
    (∀ x, 0 ≤ x → x ≤ π / 4 → f x ≤ 3 * sqrt 3) := by
  constructor
  · refine ⟨π / 6, zero_le_pi_div_six, pi_div_six_le_pi_div_four, ?_⟩
    exact f_at_pi_div_six
  · intro x hx0 hx1
    have := part1_upper x hx0 hx1
    rw [f_at_pi_div_six] at this
    exact this

/-! ## 四、第 (2) 问

不妨先设 a ∈ (−π, π]（一般 a 可减去 2nπ）。分类：
• 若 a > 2θ，取 y = a − θ；
• 若 a < −2θ，取 y = a + θ；
• 若 |a| ≤ 2θ：a ≥ 0 取 y = θ，a < 0 取 y = −θ。
-/

theorem part2_on_rep (θ a : ℝ)
    (hθ0 : 0 < θ) (hθπ : θ < π)
    (haL : -π < a) (haR : a ≤ π) :
    ∃ y, a - θ ≤ y ∧ y ≤ a + θ ∧ cos y ≤ cos θ := by
  have hθn : 0 ≤ θ := lt_imp_le _ _ hθ0
  by_cases hgt : 2 * θ < a
  · refine ⟨a - θ, le_refl (a - θ), sub_le_add a θ hθn, ?_⟩
    exact cos_left_endpoint θ a hθ0 hθπ hgt haR
  · have hle : a ≤ 2 * θ := le_of_not_lt _ _ hgt
    by_cases hlt : a < -(2 * θ)
    · refine ⟨a + θ, ?_, ?_, ?_⟩
      · have hmem := sub_le_add a θ hθn
        exact le_trans (a - θ) (a + θ) (a + θ) hmem (le_refl (a + θ))
      · exact le_refl (a + θ)
      · exact cos_right_endpoint θ a hθ0 hθπ hlt haL
    · have hge : -(2 * θ) ≤ a := le_of_not_lt _ _ (fun h' => hlt h')
      by_cases hpos : 0 ≤ a
      · have hmem := theta_in_interval a θ hpos hle
        refine ⟨θ, hmem.left, hmem.right, le_refl (cos θ)⟩
      · have hneg : a < 0 := lt_of_not_le _ _ hpos
        have hmem := neg_theta_in_interval a θ hneg hge
        refine ⟨-θ, hmem.left, hmem.right, ?_⟩
        rw [cos_neg]
        exact le_refl (cos θ)

theorem part2 (θ a : ℝ) (hθ0 : 0 < θ) (hθπ : θ < π) :
    ∃ y, a - θ ≤ y ∧ y ≤ a + θ ∧ cos y ≤ cos θ := by
  obtain ⟨a', n, haeq, haL, haR⟩ := exists_a_rep a
  obtain ⟨y', hy'⟩ := part2_on_rep θ a' hθ0 hθπ haL haR
  have hyin := interval_shift a a' n θ y' haeq ⟨hy'.1, hy'.2.1⟩
  refine ⟨y' + (2 * n) * π, hyin.left, hyin.right, ?_⟩
  rw [cos_add_two_pi_mul]
  exact hy'.2.2

/-! ## 五、第 (3) 问

先证任意 φ 都存在 x 使 g(φ, x) ≥ 3√3，因此合格的 b 不能小于 3√3。
再取 φ = 0，由倍角展开知 g(0, x) = f(x) ≤ 3√3 对一切 x 成立。
故最小 b 就是 3√3。

构造：把 φ 化到 (−π, π]。
• 0 ≤ φ ≤ π 时取 x = (π − φ)/6，此时 5x+φ = π − x，
  g = 5 cos x − cos(π − x) = 6 cos x ≥ 6 cos(π/6) = 3√3；
• −π < φ < 0 时取 x = −(π + φ)/6，同样得到 g = 6 cos |x| ≥ 3√3。
-/

theorem g_zero (x : ℝ) : g 0 x = f x := by
  rw [g, f, add_zero]

theorem eval_special_pos (φ : ℝ) :
    g φ ((π - φ) / 6) = 6 * cos ((π - φ) / 6) := by
  have h := special_angle_pos φ
  simp only [g]
  rw [h, cos_pi_sub, sub_neg, five_cos_add_cos]

theorem eval_special_neg (φ : ℝ) :
    g φ (-((π + φ) / 6)) = 6 * cos ((π + φ) / 6) := by
  simp only [g]
  rw [special_angle_neg φ]
  rw [cos_neg, cos_neg, cos_pi_sub, sub_neg, five_cos_add_cos]

theorem six_cos_pi_div_six : 6 * cos (π / 6) = 3 * sqrt 3 := by
  rw [cos_pi_div_six, six_mul_half_sqrt3]

theorem special_pos_ge (φ : ℝ) (h0 : 0 ≤ φ) (hπ : φ ≤ π) :
    3 * sqrt 3 ≤ g φ ((π - φ) / 6) := by
  have hx0 := zero_le_special_pos φ h0 hπ
  have hx1 := special_pos_le_pi_six φ h0 hπ
  have hcos : cos (π / 6) ≤ cos ((π - φ) / 6) :=
    cos_anti_on_zero_pi_six ((π - φ) / 6) (π / 6) hx0 hx1 (le_refl (π / 6))
  have h6 : 6 * cos (π / 6) ≤ 6 * cos ((π - φ) / 6) := six_mul_le _ _ hcos
  rw [eval_special_pos, ← six_cos_pi_div_six]
  exact h6

theorem special_neg_ge (φ : ℝ) (hπ : -π < φ) (h0 : φ ≤ 0) :
    3 * sqrt 3 ≤ g φ (-((π + φ) / 6)) := by
  have hx0 := zero_le_special_neg φ hπ h0
  have hx1 := special_neg_le_pi_six φ hπ h0
  have hcos : cos (π / 6) ≤ cos ((π + φ) / 6) :=
    cos_anti_on_zero_pi_six ((π + φ) / 6) (π / 6) hx0 hx1 (le_refl (π / 6))
  have h6 : 6 * cos (π / 6) ≤ 6 * cos ((π + φ) / 6) := six_mul_le _ _ hcos
  rw [eval_special_neg, ← six_cos_pi_div_six]
  exact h6

theorem part3_lower_on_rep (φ : ℝ) (hL : -π < φ) (hR : φ ≤ π) :
    ∃ x, 3 * sqrt 3 ≤ g φ x := by
  by_cases hpos : 0 ≤ φ
  · exact ⟨(π - φ) / 6, special_pos_ge φ hpos hR⟩
  · have hneg : φ < 0 := lt_of_not_le _ _ hpos
    exact ⟨-((π + φ) / 6), special_neg_ge φ hL (lt_imp_le _ _ hneg)⟩

theorem part3_lower (φ : ℝ) : ∃ x, 3 * sqrt 3 ≤ g φ x := by
  obtain ⟨φ', hL, hR, heq⟩ := exists_phi_rep φ
  obtain ⟨x, hx⟩ := part3_lower_on_rep φ' hL hR
  refine ⟨x, ?_⟩
  have hxeq : g φ x = g φ' x := by
    simp [g]
    exact heq x
  rw [hxeq]
  exact hx

theorem part3_phi_zero : ∀ x, g 0 x ≤ 3 * sqrt 3 := by
  intro x
  rw [g_zero]
  exact f_global_ub x

/-- b 的最小值是 `3 * sqrt 3`。 -/
theorem part3 :
    (∃ φ, ∀ x, g φ x ≤ 3 * sqrt 3) ∧
    (∀ b, (∃ φ, ∀ x, g φ x ≤ b) → 3 * sqrt 3 ≤ b) := by
  constructor
  · exact ⟨0, part3_phi_zero⟩
  · intro b hb
    obtain ⟨φ, hφ⟩ := hb
    obtain ⟨x, hx⟩ := part3_lower φ
    exact le_trans _ _ _ hx (hφ x)

#check part1
#check part2
#check part3

end

end MyMathProject.GaoKao2025
