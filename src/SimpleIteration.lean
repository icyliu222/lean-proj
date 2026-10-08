/-
  简单不动点迭代的收敛性证明

  迭代格式：x_{n+1} = f(x_n),  f(x) = x / 2 + 1
  初值：    x_0 = 0

  结论：序列收敛到不动点 2，且为线性收敛（每步误差减半，收敛因子 1/2）。

  闭式解：x_n = 2 - 2 · (1/2)^n
-/

import Mathlib.Analysis.SpecificLimits.Basic --提供一些极限结论
import Mathlib.Topology.Basic --提供拓扑 / 滤子基础

open Filter Topology --打开两个命名空间

namespace SimpleIteration

/-- 迭代函数 f(x) = x / 2 + 1 -/
noncomputable def f (x : ℝ) : ℝ := x / 2 + 1 --Mathlib 里实数 `ℝ` 的定义不是可计算的构造（基于柯西列 / 戴德金分割）

/-- 迭代序列：x_0 = 0，x_{n+1} = f(x_n) -/
noncomputable def seq : ℕ → ℝ
  | 0 => 0
  | n + 1 => f (seq n)

/-! ### 1. 闭式解 -/

/-- 闭式解：x_n = 2 - 2 · (1/2)^n -/
theorem seq_closed_form (n : ℕ) : seq n = 2 - 2 * (1 / 2 : ℝ)^n := by
  induction n with
  | zero =>
    norm_num [seq, f]
  | succ n ih =>
    rw [seq, f, ih] --依次重写
    field_simp
    ring

/-! ### 2. 不动点与误差 -/

/-- 2 是 f 的不动点：f(2) = 2 -/
theorem fixed_point : f 2 = 2 := by
  norm_num [f]

/-- 误差的精确表达式：|x_n - 2| = 2 · (1/2)^n -/
theorem error_formula (n : ℕ) : |seq n - 2| = 2 * (1 / 2 : ℝ)^n := by
  rw [seq_closed_form n]
  have h : (2 - 2 * (1 / 2 : ℝ)^n : ℝ) - 2 = -(2 * (1 / 2 : ℝ)^n) := by ring
  rw [h]
  rw [abs_neg, abs_of_pos]
  positivity --专门判断数值 / 代数表达式正负性的 tactic

/-! ### 3. 收敛性 -/

/-- 几何序列 (1/2)^n 趋于 0 -/
lemma half_pow_tendsto_zero :
    Tendsto (fun n : ℕ => (1 / 2 : ℝ)^n) atTop (𝓝 0) := by --`atTop`，自然数无穷远滤子；`𝓝 0`，邻域滤子
  apply tendsto_pow_atTop_nhds_zero_of_lt_one --Mathlib 现成定理
  · norm_num
  · norm_num

/-- 主定理：迭代序列 x_n 收敛到不动点 2 -/
theorem seq_converges : Tendsto seq atTop (𝓝 2) := by
  have h1 : ∀ n, seq n = 2 - 2 * (1 / 2 : ℝ)^n := seq_closed_form
  have h2 : Tendsto (fun n : ℕ => (1 / 2 : ℝ)^n) atTop (𝓝 0) :=
    half_pow_tendsto_zero
  have h3 : Tendsto (fun n : ℕ => 2 - 2 * (1 / 2 : ℝ)^n) atTop (𝓝 2) := by
    simpa using tendsto_const_nhds.sub (h2.const_mul 2)
  exact h3.congr (fun n => (h1 n).symm)

/-! ### 4. 收敛阶：线性收敛（因子 1/2） -/

/-- 误差每步恰好减半：|x_{n+1} - 2| = (1/2) · |x_n - 2| -/
theorem linear_convergence_rate (n : ℕ) :
    |seq (n + 1) - 2| = (1 / 2 : ℝ) * |seq n - 2| := by
  rw [error_formula (n + 1), error_formula n]
  field_simp
  ring

end SimpleIteration
