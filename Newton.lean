import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add

/-
  Newton's method: second-order convergence.

  Let f : ℝ → ℝ, r a simple root: f r = 0 and f' r ≠ 0.
  Newton map g(x) := x - f x / f' x.
  Key fact: g'(r) = 0, hence the error e_n = x_n - r satisfies
  e_{n+1} = g(x_n) - r = O(e_n^2) (quadratic / second-order convergence).
-/

open Set Topology Filter

namespace Newton

/-- The Newton map g(x) = x - f x / f' x. -/
noncomputable def newtonMap (f f' : ℝ → ℝ) (x : ℝ) : ℝ := x - f x / f' x

/-- Core theorem. At a simple root r (f r = 0, f' r ≠ 0), if f is differentiable
  at r with derivative f' r, and f' is differentiable at r, then the Newton map
  has derivative 0 at r.
-/
theorem newtonMap_deriv_at_simple_root
    (f f' f2 : ℝ → ℝ) (r : ℝ)
    (hf : HasDerivAt f (f' r) r)
    (hf' : HasDerivAt f' (f2 r) r)
    (hr : f r = 0)
    (hne : f' r ≠ 0) :
    HasDerivAt (newtonMap f f') 0 r := by
  -- d/dx [f x / f' x] at r = (f' r * f' r - f r * f2 r) / (f' r)^2
  have hdiv : HasDerivAt (fun x => f x / f' x)
        ((f' r * f' r - f r * f2 r) / (f' r)^2) r :=
    HasDerivAt.div hf hf' hne
  -- substitute f r = 0  ⇒  this derivative equals 1
  have hdiv1 : (f' r * f' r - f r * f2 r) / (f' r)^2 = 1 := by
    rw [hr]
    field_simp [hne, pow_two]
    ring
  rw [hdiv1] at hdiv
  -- g(x) = x - f x / f' x, so g'(r) = 1 - 1 = 0
  have h := HasDerivAt.sub (hasDerivAt_id r) hdiv
  convert h using 1
  · funext x; rfl
  · ring

end Newton
