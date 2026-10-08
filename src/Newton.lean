import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-
  Newton's method: second-order convergence.

  Let f : ℝ → ℝ, r a simple root: f r = 0 and f' r ≠ 0.
  Newton map g(x) := x - f x / f' x.

  Two facts we prove here:
    (1) g'(r) = 0.
        ⇒ error e_n = x_n - r satisfies e_{n+1} = O(e_n^2)   (at least 2nd order).
    (2) g''(r) = f''(r) / f'(r).
        If additionally f''(r) ≠ 0, then g''(r) ≠ 0.
        ⇒ convergence order is *exactly* 2 (quadratic).
-/

open Set Topology Filter

namespace Newton

/-! ### 1. 牛顿映射的定义 -/

/-- The Newton map g(x) = x - f x / f' x. -/
noncomputable def newtonMap (f f' : ℝ → ℝ) (x : ℝ) : ℝ :=
  x - f x / f' x

/-! ### 2. 核心一阶结论：g'(r) = 0 -/

/-- 在单根 r 处，牛顿映射的一阶导数为 0。
    这只用到 f 在 r 可导、f' 在 r 可导、f r = 0、f' r ≠ 0。 -/
theorem newtonMap_deriv_at_simple_root
    (f f' f2 : ℝ → ℝ) (r : ℝ)
    (hf : HasDerivAt f (f' r) r) -- f 在 r 的导数 = f'(r)
    (hf' : HasDerivAt f' (f2 r) r) -- f' 在 r 的导数 = f''(r)
    (hr : f r = 0) -- r 是根
    (hne : f' r ≠ 0) -- 单根条件
    : HasDerivAt (newtonMap f f') 0 r := by
  -- (a) 先求分式 h(x) = f x / f' x 在 r 的导数（商求导法则）
  have h1 : HasDerivAt (fun x ↦ f x / f' x)
        ((f' r * f' r - f r * f2 r) / (f' r)^2) r :=
    HasDerivAt.div hf hf' hne
  -- (b) 把 f r = 0 代入，该导数化简为 1
  have h2 : (f' r * f' r - f r * f2 r) / (f' r)^2 = 1 := by
    rw [hr]
    field_simp [hne, pow_two]
    ring
  rw [h2] at h1
  -- (c) g(x) = x - h(x)，故 g'(r) = (x)' - h'(r) = 1 - 1 = 0
  have h := HasDerivAt.sub (hasDerivAt_id r) h1
  -- (d) 对齐 newtonMap 的定义，并把 1 - 1 化简为 0
  convert h using 1
  · funext x; rfl   -- newtonMap f f' = (fun x ↦ x - f x / f' x)，按定义相等
  · ring            -- 1 - 1 = 0

/-! ### 3. 二阶结论：g''(r) = f''(r) / f'(r) -/

/-- 先把牛顿映射的一阶导函数 g'(x) 显式算出来。
    对 g(x) = x - f(x)/f'(x) 求导：
      g'(x) = 1 - [f'(x)^2 - f(x) f''(x)] / f'(x)^2
            = f(x) * f''(x) / f'(x)^2
    注意这是一个"逐点"的导数表达式，不要求 f(x)=0。 -/
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
  · -- 1 - (f' x * f' x - f x * f2 x) / (f' x)^2 = f x * f2 x / (f' x)^2
    field_simp [hx, pow_two]
    ring

lemma newtonMap_deriv_eq (f f' f2 : ℝ → ℝ) (x : ℝ) (hx : f' x ≠ 0)
  (hf : HasDerivAt f (f' x) x)
  (hf' : HasDerivAt f' (f2 x) x) :
  deriv (newtonMap f f') x = (f x * f2 x) / (f' x)^2 := by
  have h_hasderiv : HasDerivAt (newtonMap f f') (f x * f2 x / (f' x)^2) x :=
    newtonMap_deriv_formula f f' f2 x hx hf hf'
  exact h_hasderiv.deriv

/-- 在单根 r 处，牛顿映射的二阶导数
      g''(r) = f''(r) / f'(r)。
    若 f''(r) ≠ 0，则 g''(r) ≠ 0，从而迭代恰好二阶收敛。

    额外假设：f2（即 f''）在 r 处可导，导数值为 f3 r（即 f'''(r)）。
    这是为了对分子 f(x) * f2(x) 使用乘积求导法则所必需的。 -/
theorem newtonMap_second_deriv_at_simple_root
    (f f' f2 f3 : ℝ → ℝ) (r : ℝ)
    (hf_all : ∀ x, HasDerivAt f (f' x) x) -- f' 是f的导函数，处处成立
    (hf'_all : ∀ x, HasDerivAt f' (f2 x) x) -- f2 是f'的导函数，处处成立
    (hf2_all : ∀ x, HasDerivAt f2 (f3 x) x)
    (hr : f r = 0)
    (hne_all : ∀ x, f' x ≠ 0) -- f'处处不为0
    : HasDerivAt (fun x ↦ deriv (newtonMap f f') x) (f2 r / f' r) r := by
  -- 记分子 N(x) := f x * f2 x，分母 D(x) := (f' x)^2。
  -- 由 newtonMap_deriv_formula，g'(x) = N(x) / D(x)。
  -- 我们对这个商在 r 处再求一次导。

  -- (a) D(x) = (f' x)^2 在 r 的导数：2 * f'(r) * f''(r)
  have hD_mul : HasDerivAt (fun x ↦ f' x * f' x)
    (f2 r * f' r + f' r * f2 r) r :=
    HasDerivAt.mul (hf'_all r) (hf'_all r)
  have h_fun_eq : (fun x : ℝ ↦ f' x * f' x) = (fun x : ℝ ↦ f' x ^ 2) := by
    funext x
    ring
  have hD_pow : HasDerivAt (fun x ↦ f' x ^ 2) (2 * f' r * f2 r) r := by
    convert hD_mul using 1
    · rw [h_fun_eq]
    · ring
  have hD_ne : (f' r)^2 ≠ 0 := pow_ne_zero 2 (hne_all r)
  -- (b) N(x) = f x * f2 x 在 r 的导数：f'(r)*f2(r) + f(r)*f3(r)
  have hN : HasDerivAt (fun x ↦ f x * f2 x)
        (f' r * f2 r + f r * f3 r) r :=
    HasDerivAt.mul (hf_all r) (hf2_all r)
  -- (c) 商法则：(N/D)'(r) = [N'(r) D(r) - N(r) D'(r)] / D(r)^2
  have h1 : HasDerivAt (fun x ↦ (f x * f2 x) / (f' x)^2)
        (((f' r * f2 r + f r * f3 r) * (f' r)^2
          - (f r * f2 r) * (2 * (f' r) * f2 r)) / (f' r ^ 2) ^ 2) r :=
    HasDerivAt.div hN hD_pow hD_ne
  -- (d) 代入 f r = 0，分子里所有含 f r 的项都消掉：
  --     分子 = f'(r) * f2 r * (f' r)^2 = f2 r * (f' r)^3
  --     分母 = (f' r ^ 2) ^ 2)
  --     比值 = f2 r / f' r
  have h_simp :
      (((f' r * f2 r + f r * f3 r) * (f' r)^2
        - (f r * f2 r) * (2 * (f' r) * f2 r)) / (f' r ^ 2) ^ 2)
      = f2 r / f' r := by
    rw [hr]
    field_simp [hne_all r, pow_two]
    ring
  rw [h_simp] at h1
  -- (e) 把 "fun x ↦ deriv (newtonMap f f') x" 与
  --     "fun x ↦ (f x * f2 x) / (f' x)^2" 对齐：
  --     这两个函数在 r 的某个邻域内相等，由 newtonMap_deriv_formula 给出。
  convert h1 using 1
  · funext x
    have h_eq : deriv (newtonMap f f') x = (f x * f2 x) / (f' x)^2 :=
      newtonMap_deriv_eq f f' f2 x (hne_all x) (hf_all x) (hf'_all x)
    exact h_eq


/-- 推论：在单根 r 处，若 f''(r) ≠ 0，则牛顿映射的二阶导数非零。
    这正是"恰好二次收敛"的非零条件。 -/
theorem newtonMap_second_deriv_ne_zero
    (f f' f2 f3 : ℝ → ℝ) (r : ℝ)
    (_hf_all : ∀ x, HasDerivAt f (f' x) x)
    (_hf'_all : ∀ x, HasDerivAt f' (f2 x) x)
    (_hf2_all : ∀ x, HasDerivAt f2 (f3 x) x)
    (_hr : f r = 0)
    (hne_all : ∀ x, f' x ≠ 0)
    (hf2' : f2 r ≠ 0) -- 额外的非零假设
    : (f2 r / f' r : ℝ) ≠ 0 := by
  exact div_ne_zero hf2' (hne_all r)

end Newton
