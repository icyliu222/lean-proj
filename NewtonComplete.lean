import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LHopital

/-
  Newton's method: exact second-order (quadratic) convergence.

  设 f : ℝ → ℝ，r 是单根：f r = 0 且 f' r ≠ 0。
  牛顿映射 g(x) := x - f x / f' x，迭代 x_{n+1} = g(x_n)，误差 e_n := x_n - r。

  完整证明链条：
    (1) g'(x) = f(x)·f''(x)/f'(x)²  （逐点一阶导数公式）
    (2) g'(r) = 0                      （单根处一阶导数为零 ⇒ 至少二阶收敛）
    (3) g''(r) = f''(r)/f'(r)          （单根处二阶导数，仅需 f'' 在 r 连续，不需 f'''）
    (4) 二阶 Peano 泰勒展开：若 g'(r)=0 且 g''(r) 存在，
        则 (g(x)-g(r))/(x-r)² → g''(r)/2
    (5) 误差比 e_{n+1}/e_n² → f''(r)/(2f'(r))
    (6) 若 f''(r) ≠ 0，则该极限非零 ⇒ 收敛阶恰好为 2

  假设清单（主定理 newton_exact_quadratic_convergence）：
    · f 处处可导，导函数为 f'
    · f' 处处可导，导函数为 f2（即 f''）
    · f2 在 r 处连续（ContinuousAt f2 r）
    · f r = 0，f' r ≠ 0（单根）
    · f2 r ≠ 0（f''(r) ≠ 0，保证极限非零）
    · f' 处处非零（保证牛顿映射处处良定义）
    · 迭代序列 x_n → r 且 x_n ≠ r（条件收敛 + 避免除零）
-/

open Set Topology Filter

namespace Newton

/-! ### 1. 牛顿映射 -/

/-- The Newton map g(x) = x - f x / f' x. -/
noncomputable def newtonMap (f f' : ℝ → ℝ) (x : ℝ) : ℝ :=
  x - f x / f' x

/-! ### 2. 一阶导数公式 -/

/-- 牛顿映射的一阶导函数：g'(x) = f(x)·f''(x)/f'(x)²。
    对 g(x) = x - f(x)/f'(x) 求导即得，不要求 f(x)=0。 -/
lemma newtonMap_deriv_formula
    (f f' f2 : ℝ → ℝ) (x : ℝ) (hx : f' x ≠ 0)
    (hf : HasDerivAt f (f' x) x)
    (hf' : HasDerivAt f' (f2 x) x) :
    HasDerivAt (newtonMap f f') (f x * f2 x / (f' x)^2) x := by
  have h1 : HasDerivAt (fun y ↦ f y / f' y)
        ((f' x * f' x - f x * f2 x) / (f' x)^2) x :=
    HasDerivAt.div hf hf' hx
  have h := HasDerivAt.sub (hasDerivAt_id x) h1
  convert h using 1
  · funext y; rfl
  · field_simp [hx, pow_two]; ring

/-- `deriv` 形式的一阶导数公式。 -/
lemma newtonMap_deriv_eq (f f' f2 : ℝ → ℝ) (x : ℝ) (hx : f' x ≠ 0)
    (hf : HasDerivAt f (f' x) x)
    (hf' : HasDerivAt f' (f2 x) x) :
    deriv (newtonMap f f') x = (f x * f2 x) / (f' x)^2 :=
  (newtonMap_deriv_formula f f' f2 x hx hf hf').deriv

/-! ### 3. 单根处 g'(r) = 0 -/

/-- 在单根 r 处，牛顿映射的一阶导数为 0。
    这只用到 f 在 r 可导、f' 在 r 可导、f r = 0、f' r ≠ 0。
    g'(r)=0 意味着误差 e_{n+1} = O(e_n²)，即至少二阶收敛。 -/
theorem newtonMap_deriv_at_simple_root
    (f f' f2 : ℝ → ℝ) (r : ℝ)
    (hf : HasDerivAt f (f' r) r)
    (hf' : HasDerivAt f' (f2 r) r)
    (hr : f r = 0)
    (hne : f' r ≠ 0) :
    HasDerivAt (newtonMap f f') 0 r := by
  have h1 : HasDerivAt (fun x ↦ f x / f' x)
        ((f' r * f' r - f r * f2 r) / (f' r)^2) r :=
    HasDerivAt.div hf hf' hne
  have h2 : (f' r * f' r - f r * f2 r) / (f' r)^2 = 1 := by
    rw [hr]; field_simp [hne, pow_two]; ring
  rw [h2] at h1
  have h := HasDerivAt.sub (hasDerivAt_id r) h1
  convert h using 1
  · funext x; rfl
  · ring

/-! ### 4. 单根处 g''(r) = f''(r)/f'(r) -/

/-- 在单根 r 处，牛顿映射的二阶导数 g''(r) = f''(r)/f'(r)。

    关键：本证明不假设 f''' 存在。直接用导数定义：
      g''(r) = lim_{x→r} (g'(x)-g'(r))/(x-r)
             = lim_{x→r} [f(x)/(x-r)] · [f''(x)/(f'(x))²]
             = f'(r) · f''(r)/(f'(r))²
             = f''(r)/f'(r)
    只需 f'' 在 r 处连续（ContinuousAt f2 r）。
    若 f''(r) ≠ 0，则 g''(r) ≠ 0，为"恰好二阶收敛"提供非零条件。 -/
theorem newtonMap_second_deriv_at_simple_root
    (f f' f2 : ℝ → ℝ) (r : ℝ)
    (hf_all : ∀ x, HasDerivAt f (f' x) x)
    (hf'_all : ∀ x, HasDerivAt f' (f2 x) x)
    (hf2_cont : ContinuousAt f2 r)
    (hr : f r = 0)
    (hne_all : ∀ x, f' x ≠ 0) :
    HasDerivAt (fun x ↦ deriv (newtonMap f f') x) (f2 r / f' r) r := by
  set g := newtonMap f f' with hg_def
  set L := f2 r / f' r with hL_def
  -- g'(x) = f(x)·f''(x)/(f'(x))² 对所有 x 成立
  have hg'_eq : ∀ x, deriv g x = (f x * f2 x) / (f' x)^2 := by
    intro x
    exact newtonMap_deriv_eq f f' f2 x (hne_all x) (hf_all x) (hf'_all x)
  -- g'(r) = 0
  have hg'_r : deriv g r = 0 :=
    (newtonMap_deriv_at_simple_root f f' f2 r (hf_all r) (hf'_all r) hr (hne_all r)).deriv
  -- f' 在 r 连续（因 f' 在 r 可导）
  have hf'_cont : ContinuousAt f' r := (hf'_all r).continuousAt
  -- 因子1：f(x)/(x-r) → f'(r)（因 f(r)=0，这就是 f 在 r 的差商）
  have h_factor1 : Tendsto (fun x : ℝ ↦ f x / (x - r)) (𝓝[≠] r) (𝓝 (f' r)) := by
    have h_slope : Tendsto (slope f r) (𝓝[≠] r) (𝓝 (f' r)) := (hf_all r).tendsto_slope
    have h_eq : slope f r = (fun x : ℝ ↦ f x / (x - r)) := by
      funext x; rw [slope_def_field, hr]; ring
    rw [h_eq] at h_slope
    exact h_slope
  -- 因子2：f''(x)/(f'(x))² → f''(r)/(f'(r))²（f'' 连续 + f' 连续非零）
  have h_factor2 : Tendsto (fun x : ℝ ↦ f2 x / (f' x)^2) (𝓝 r) (𝓝 (f2 r / (f' r)^2)) := by
    apply Tendsto.div
    · exact hf2_cont.tendsto
    · exact hf'_cont.tendsto.pow 2
    · exact pow_ne_zero 2 (hne_all r)
  -- 乘积 → f'(r) · f''(r)/(f'(r))² = f''(r)/f'(r) = L
  have h_prod : Tendsto (fun x : ℝ ↦ (f x / (x - r)) * (f2 x / (f' x)^2))
      (𝓝[≠] r) (𝓝 ((f' r) * (f2 r / (f' r)^2))) :=
    h_factor1.mul (tendsto_nhdsWithin_of_tendsto_nhds h_factor2)
  have h_simp : (f' r) * (f2 r / (f' r)^2) = L := by
    simp only [hL_def]; field_simp [hne_all r, pow_two]
  rw [h_simp] at h_prod
  -- 对齐：(g'(x)-g'(r))/(x-r) = [f(x)/(x-r)] · [f''(x)/(f'(x))²]（去心邻域内）
  have h_align : (fun x : ℝ ↦ (deriv g x - deriv g r) / (x - r)) =ᶠ[𝓝[≠] r]
      (fun x : ℝ ↦ (f x / (x - r)) * (f2 x / (f' x)^2)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxr : x - r ≠ 0 := sub_ne_zero.mpr hx
    calc
      (deriv g x - deriv g r) / (x - r)
        = ((f x * f2 x) / (f' x)^2 - 0) / (x - r) := by rw [hg'_eq x, hg'_r]
      _ = (f x / (x - r)) * (f2 x / (f' x)^2) := by
        field_simp [hxr, hne_all x, pow_two]; ring
  -- slope (deriv g) r = (deriv g x - deriv g r)/(x-r)，转为标准形式
  have h_slope_g : slope (fun x ↦ deriv g x) r =
      (fun x : ℝ ↦ (deriv g x - deriv g r) / (x - r)) := by
    funext x; rw [slope_def_field]
  have h_main : Tendsto (slope (fun x ↦ deriv g x) r) (𝓝[≠] r) (𝓝 L) := by
    rw [h_slope_g]
    exact h_prod.congr' h_align.symm
  -- 由差商极限存在 ⇒ HasDerivAt
  exact hasDerivAt_iff_tendsto_slope.mpr h_main

/-! ### 5. 不动点与迭代序列 -/

/-- r 是牛顿映射的不动点：g(r) = r - f(r)/f'(r) = r。 -/
theorem newtonMap_fixed_point (f f' : ℝ → ℝ) (r : ℝ)
    (hr : f r = 0) (_hne : f' r ≠ 0) :
    newtonMap f f' r = r := by
  simp [newtonMap, hr]

/-- 牛顿迭代序列：x_0 为初值，x_{n+1} = g(x_n)。 -/
noncomputable def newtonSeq (f f' : ℝ → ℝ) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | n + 1 => newtonMap f f' (newtonSeq f f' x0 n)

/-! ### 6. 二阶 Peano 泰勒展开（核心引理） -/

/-- 辅助：(y-r)² 的导数为 2(x-r)。 -/
private lemma hasDerivAt_sq_sub_const (r x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (y - r)^2) (2 * (x - r)) x := by
  have h_id : HasDerivAt (fun y : ℝ ↦ y - r) (1 : ℝ) x := by
    have h1 : HasDerivAt (fun y : ℝ ↦ y) (1 : ℝ) x := hasDerivAt_id x
    have h2 : HasDerivAt (fun y : ℝ ↦ r) (0 : ℝ) x := hasDerivAt_const x r
    have h3 := h1.sub h2
    have h4 : ((fun y : ℝ ↦ y) - (fun y : ℝ ↦ r)) = (fun y : ℝ ↦ y - r) := by
      funext y; rfl
    rw [h4] at h3
    simpa using h3
  have h_mul := HasDerivAt.mul h_id h_id
  have h5 : ((fun y : ℝ ↦ y - r) * (fun y : ℝ ↦ y - r)) = (fun y : ℝ ↦ (y - r)^2) := by
    funext y; simp [pow_two]
  rw [h5] at h_mul
  have h6 : (1 * (x - r) + (x - r) * 1 : ℝ) = 2 * (x - r) := by ring
  rw [h6] at h_mul
  exact h_mul

/-- 辅助：g(y)-g(r) 的导数为 g'(x)。 -/
private lemma hasDerivAt_sub_const (g : ℝ → ℝ) (r x : ℝ)
    (hg : HasDerivAt g (deriv g x) x) :
    HasDerivAt (fun y : ℝ ↦ g y - g r) (deriv g x) x := by
  have h2 : HasDerivAt (fun y : ℝ ↦ g r) (0 : ℝ) x := hasDerivAt_const x (g r)
  have h3 := hg.sub h2
  have h4 : (g - (fun y : ℝ ↦ g r)) = (fun y : ℝ ↦ g y - g r) := by funext y; rfl
  rw [h4] at h3
  simpa using h3

/-- 通用引理：若 g 处处可导，g'(r)=0，且 g' 在 r 处可导（二阶导数为 g2），
    则当 x → r（x ≠ r）时，(g(x)-g(r))/(x-r)² → g2/2。

    证明：对分子 g(x)-g(r) 和分母 (x-r)² 使用去心邻域版洛必达法则
    `HasDerivAt.lhopital_zero_nhdsNE`（分母导数 2(x-r) 在 r 处为零，
    完整邻域版无法满足"分母导数非零"，故必须用去心邻域版）。
    导数比 g'(x)/(2(x-r)) = (g'(x)-g'(r))/(2(x-r)) → g''(r)/2。 -/
lemma second_order_peano_expansion
    (g : ℝ → ℝ) (r g2 : ℝ)
    (hg_diff : ∀ x, HasDerivAt g (deriv g x) x)
    (hg1_r : deriv g r = 0)
    (hg2_r : HasDerivAt (deriv g) g2 r)
    : Tendsto (fun x ↦ (g x - g r) / (x - r)^2) (𝓝[≠] r) (𝓝 (g2 / 2)) := by
  set f := fun x : ℝ ↦ g x - g r with hf_def
  set h := fun x : ℝ ↦ (x - r)^2 with hh_def
  set f' := fun x : ℝ ↦ deriv g x with hf'_def
  set h' := fun x : ℝ ↦ 2 * (x - r) with hh'_def
  -- (a) f 在去心邻域内可导，导数为 f'(x)
  have h1 : ∀ᶠ x in 𝓝[≠] r, HasDerivAt f (f' x) x := by
    have h_all : ∀ (x : ℝ), HasDerivAt f (f' x) x := by
      intro x
      simp only [hf_def, hf'_def]
      exact hasDerivAt_sub_const g r x (hg_diff x)
    exact Filter.Eventually.of_forall h_all
  -- (b) h 在去心邻域内可导，导数为 h'(x)
  have h2 : ∀ᶠ x in 𝓝[≠] r, HasDerivAt h (h' x) x := by
    have h_all : ∀ (x : ℝ), HasDerivAt h (h' x) x := by
      intro x
      simp only [hh_def, hh'_def]
      exact hasDerivAt_sq_sub_const r x
    exact Filter.Eventually.of_forall h_all
  -- (c) h'(x)=2(x-r) 在去心邻域内非零
  have h3 : ∀ᶠ x in 𝓝[≠] r, h' x ≠ 0 := by
    have h_all : ∀ (x : ℝ), x ≠ r → h' x ≠ 0 := by
      intro x hx
      simp only [hh'_def]
      exact mul_ne_zero two_ne_zero (sub_ne_zero.mpr hx)
    exact eventually_nhdsWithin_of_forall h_all
  -- (d) f(x)=g(x)-g(r) → 0
  have h4 : Tendsto f (𝓝[≠] r) (𝓝 0) := by
    have h_cont : ContinuousAt g r := (hg_diff r).continuousAt
    have h_const : Tendsto (fun y : ℝ ↦ g r) (𝓝 r) (𝓝 (g r)) := tendsto_const_nhds
    have h_t : Tendsto (fun x ↦ g x - g r) (𝓝 r) (𝓝 0) := by
      have h := h_cont.tendsto.sub h_const
      simpa using h
    simpa [hf_def] using tendsto_nhdsWithin_of_tendsto_nhds h_t
  -- (e) h(x)=(x-r)² → 0
  have h5 : Tendsto h (𝓝[≠] r) (𝓝 0) := by
    have h_const : Tendsto (fun y : ℝ ↦ r) (𝓝 r) (𝓝 r) := tendsto_const_nhds
    have h_sub : Tendsto (fun x ↦ x - r) (𝓝 r) (𝓝 0) := by
      have h := tendsto_id.sub h_const
      simpa using h
    have h_pow : Tendsto (fun x ↦ (x - r)^2) (𝓝 r) (𝓝 0) := by
      have h := h_sub.pow 2
      simpa using h
    simpa [hh_def] using tendsto_nhdsWithin_of_tendsto_nhds h_pow
  -- (f) 导数比 f'(x)/h'(x) = g'(x)/(2(x-r)) → g2/2
  -- 斜率：(g'(x)-g'(r))/(x-r) → g2
  have h_littleo : (fun x : ℝ ↦ deriv g x - deriv g r - (x - r) * g2) =o[𝓝 r] (fun x : ℝ ↦ x - r) :=
    hg2_r.isLittleO
  have h_q : Tendsto (fun x : ℝ ↦ (deriv g x - deriv g r - (x - r) * g2) / (x - r)) (𝓝[≠] r) (𝓝 0) := by
    have h_q_nhds : Tendsto (fun x : ℝ ↦ (deriv g x - deriv g r - (x - r) * g2) / (x - r)) (𝓝 r) (𝓝 0) :=
      h_littleo.tendsto_div_nhds_zero
    exact tendsto_nhdsWithin_of_tendsto_nhds h_q_nhds
  set F := fun x : ℝ ↦ (deriv g x - deriv g r) / (x - r) - g2 with hF_def
  set G := fun x : ℝ ↦ (deriv g x - deriv g r - (x - r) * g2) / (x - r) with hG_def
  have h_eq2' : G =ᶠ[𝓝[≠] r] F := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [hF_def, hG_def]
    have hxr : x - r ≠ 0 := sub_ne_zero.mpr hx
    field_simp [hxr]
  have h_q' : Tendsto F (𝓝[≠] r) (𝓝 0) := h_q.congr' h_eq2'
  have h_const_g2 : Tendsto (fun _ : ℝ ↦ g2) (𝓝[≠] r) (𝓝 g2) := tendsto_const_nhds
  have h_slope : Tendsto (fun x : ℝ ↦ (deriv g x - deriv g r) / (x - r)) (𝓝[≠] r) (𝓝 g2) := by
    have h_add_raw : Tendsto (fun x : ℝ ↦ F x + g2) (𝓝[≠] r) (𝓝 (0 + g2)) := h_q'.add h_const_g2
    have h_add : Tendsto (fun x : ℝ ↦ F x + g2) (𝓝[≠] r) (𝓝 g2) := by simpa using h_add_raw
    have h_eq : (fun x : ℝ ↦ F x + g2) = (fun x : ℝ ↦ (deriv g x - deriv g r) / (x - r)) := by
      funext x; simp [hF_def]
    rw [h_eq] at h_add
    exact h_add
  have h6 : Tendsto (fun x ↦ f' x / h' x) (𝓝[≠] r) (𝓝 (g2 / 2)) := by
    have h_eq : ∀ (x : ℝ), f' x / h' x = (deriv g x - deriv g r) / (2 * (x - r)) := by
      intro x
      simp only [hf'_def, hh'_def, hg1_r]; ring
    simp_rw [h_eq]
    have h_align : (fun x : ℝ ↦ (1 / 2 : ℝ) * ((deriv g x - deriv g r) / (x - r)))
        = (fun x : ℝ ↦ (deriv g x - deriv g r) / (2 * (x - r))) := by
      funext x
      by_cases hx : x = r
      · simp [hx]
      · field_simp [hx]
    have h_val : (g2 / 2 : ℝ) = (1 / 2 : ℝ) * g2 := by ring
    have h_const_mul : Tendsto (fun x : ℝ ↦ (1 / 2 : ℝ) * ((deriv g x - deriv g r) / (x - r))) (𝓝[≠] r) (𝓝 (g2 / 2)) := by
      rw [h_val]
      exact h_slope.const_mul (1 / 2 : ℝ)
    exact h_const_mul.congr (congrFun h_align)
  -- (g) 应用洛必达法则
  have h_main : Tendsto (fun x ↦ f x / h x) (𝓝[≠] r) (𝓝 (g2 / 2)) :=
    HasDerivAt.lhopital_zero_nhdsNE h1 h2 h3 h4 h5 h6
  simpa [hf_def, hh_def] using h_main

/-! ### 7. 牛顿映射处处可导 -/

/-- 牛顿映射 g 处处可导，导数为 deriv g x。
    由一阶导数公式 `newtonMap_deriv_formula` 直接得到。 -/
lemma newtonMap_hasDerivAt_everywhere
    (f f' f2 : ℝ → ℝ)
    (hf_all : ∀ x, HasDerivAt f (f' x) x)
    (hf'_all : ∀ x, HasDerivAt f' (f2 x) x)
    (hne_all : ∀ x, f' x ≠ 0) :
    ∀ (x : ℝ), HasDerivAt (newtonMap f f') (deriv (newtonMap f f') x) x := by
  intro x
  have h_formula : HasDerivAt (newtonMap f f') (f x * f2 x / (f' x)^2) x :=
    newtonMap_deriv_formula f f' f2 x (hne_all x) (hf_all x) (hf'_all x)
  have h_eq : deriv (newtonMap f f') x = (f x * f2 x) / (f' x)^2 :=
    newtonMap_deriv_eq f f' f2 x (hne_all x) (hf_all x) (hf'_all x)
  rw [h_eq]
  exact h_formula

/-! ### 8. 误差比收敛 -/

/-- 误差比收敛定理：若牛顿迭代 x_n → r（且 x_n ≠ r），
    则 e_{n+1}/e_n² → f''(r)/(2f'(r))。

    注意：不需要 f''' 存在，只需 f'' 在 r 连续。 -/
theorem newton_error_ratio_tendsto
    (f f' f2 : ℝ → ℝ) (r : ℝ) (x0 : ℝ)
    (hf_all : ∀ x, HasDerivAt f (f' x) x)
    (hf'_all : ∀ x, HasDerivAt f' (f2 x) x)
    (hf2_cont : ContinuousAt f2 r)
    (hr : f r = 0)
    (hne_all : ∀ x, f' x ≠ 0)
    (hne_seq : ∀ n, newtonSeq f f' x0 n ≠ r)
    (hconv : Tendsto (newtonSeq f f' x0) atTop (𝓝 r)) :
    Tendsto (fun n ↦ (newtonSeq f f' x0 (n + 1) - r) / (newtonSeq f f' x0 n - r)^2)
      atTop (𝓝 (f2 r / (2 * f' r))) := by
  set g := newtonMap f f' with hg_def
  set g2 := f2 r / f' r with hg2_def
  have hg_diff : ∀ x, HasDerivAt g (deriv g x) x :=
    newtonMap_hasDerivAt_everywhere f f' f2 hf_all hf'_all hne_all
  have hg1_r : deriv g r = 0 :=
    (newtonMap_deriv_at_simple_root f f' f2 r (hf_all r) (hf'_all r) hr (hne_all r)).deriv
  have hg2_r : HasDerivAt (deriv g) g2 r :=
    newtonMap_second_deriv_at_simple_root f f' f2 r
      hf_all hf'_all hf2_cont hr hne_all
  have hg_fixed : g r = r :=
    newtonMap_fixed_point f f' r hr (hne_all r)
  have h_taylor : Tendsto (fun x ↦ (g x - g r) / (x - r)^2) (𝓝[≠] r) (𝓝 (g2 / 2)) :=
    second_order_peano_expansion g r g2 hg_diff hg1_r hg2_r
  have h_main : Tendsto (fun x ↦ (g x - r) / (x - r)^2) (𝓝[≠] r) (𝓝 (f2 r / (2 * f' r))) := by
    have h_eq1 : (fun x : ℝ ↦ (g x - r) / (x - r)^2) = (fun x : ℝ ↦ (g x - g r) / (x - r)^2) := by
      funext x; rw [hg_fixed]
    rw [h_eq1]
    have h_val : g2 / 2 = f2 r / (2 * f' r) := by
      simp only [hg2_def]; ring
    rw [h_val] at h_taylor
    exact h_taylor
  -- 序列 x_n → r 且 x_n ≠ r，故 x_n → r（去心邻域滤子）
  have hseq_nhds_ne : Tendsto (newtonSeq f f' x0) atTop (𝓝[≠] r) := by
    have h1 : Tendsto (newtonSeq f f' x0) atTop (𝓝 r) := hconv
    have h2' : ∀ᶠ (n : ℕ) in atTop, newtonSeq f f' x0 n ∈ ({r}ᶜ : Set ℝ) :=
      Filter.Eventually.of_forall hne_seq
    have h2 : Tendsto (newtonSeq f f' x0) atTop (𝓟 ({r}ᶜ : Set ℝ)) :=
      tendsto_principal.mpr h2'
    have h3 : 𝓝[≠] r = 𝓝 r ⊓ 𝓟 ({r}ᶜ : Set ℝ) := by
      simp [nhdsWithin]
    rw [h3]
    have h4 := h1.inf h2
    simpa [inf_idem] using h4
  have h_comp : Tendsto (fun n ↦ (g (newtonSeq f f' x0 n) - r) / (newtonSeq f f' x0 n - r)^2)
      atTop (𝓝 (f2 r / (2 * f' r))) :=
    h_main.comp hseq_nhds_ne
  have h_final : (fun n : ℕ ↦ (g (newtonSeq f f' x0 n) - r) / (newtonSeq f f' x0 n - r)^2) =
      (fun n : ℕ ↦ (newtonSeq f f' x0 (n + 1) - r) / (newtonSeq f f' x0 n - r)^2) := by
    funext n
    rw [hg_def]
    simp [newtonSeq]
  rw [h_final] at h_comp
  exact h_comp

/-! ### 9. 恰好二阶收敛（主定理） -/

/-- 主定理：恰好二阶收敛（quadratic convergence）。

    设 r 是 f 的单根（f(r)=0, f'(r)≠0），且 f''(r)≠0，f'' 在 r 处连续。
    若牛顿迭代 x_{n+1}=g(x_n) 收敛到 r（且 x_n≠r），则误差 e_n=x_n-r 满足
      e_{n+1}/e_n² → f''(r)/(2f'(r)) ≠ 0。

    极限非零意味着：
      · e_{n+1} = O(e_n²)（至少二次衰减）
      · e_{n+1} ≠ o(e_n²)（不是高于二次的衰减）
    因此收敛阶恰好为 2。

    假设清单：
      (1) f 处处可导，f' 处处可导（f''=f2 处处存在）
      (2) f'' 在 r 处连续（不需 f'''）
      (3) f(r)=0, f'(r)≠0（单根）
      (4) f''(r)≠0（极限非零）
      (5) f' 处处非零（牛顿映射良定义）
      (6) x_n→r 且 x_n≠r（条件收敛 + 避免除零） -/
theorem newton_exact_quadratic_convergence
    (f f' f2 : ℝ → ℝ) (r : ℝ) (x0 : ℝ)
    (hf_all : ∀ x, HasDerivAt f (f' x) x)
    (hf'_all : ∀ x, HasDerivAt f' (f2 x) x)
    (hf2_cont : ContinuousAt f2 r)
    (hr : f r = 0)
    (hne_all : ∀ x, f' x ≠ 0)
    (hf2' : f2 r ≠ 0)
    (hne_seq : ∀ n, newtonSeq f f' x0 n ≠ r)
    (hconv : Tendsto (newtonSeq f f' x0) atTop (𝓝 r)) :
    Tendsto (fun n ↦ (newtonSeq f f' x0 (n + 1) - r) / (newtonSeq f f' x0 n - r)^2)
      atTop (𝓝 (f2 r / (2 * f' r)))
    ∧ (f2 r / (2 * f' r) : ℝ) ≠ 0 := by
  have h_ratio : Tendsto (fun n ↦ (newtonSeq f f' x0 (n + 1) - r) / (newtonSeq f f' x0 n - r)^2)
      atTop (𝓝 (f2 r / (2 * f' r))) :=
    newton_error_ratio_tendsto f f' f2 r x0
      hf_all hf'_all hf2_cont hr hne_all hne_seq hconv
  have h_nonzero : (f2 r / (2 * f' r) : ℝ) ≠ 0 := by
    apply div_ne_zero
    · exact hf2'
    · exact mul_ne_zero two_ne_zero (hne_all r)
  exact ⟨h_ratio, h_nonzero⟩

end Newton
