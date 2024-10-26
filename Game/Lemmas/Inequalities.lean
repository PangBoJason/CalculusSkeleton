import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Real

namespace CGame

lemma sin_sq_lt_sq (hx : x ≠ 0) : sin x ^ 2 < x ^ 2 := by
  wlog hx₀ : 0 < x
  case inr =>
    simpa using this (neg_ne_zero.2 hx) <| neg_pos_of_neg <| hx.lt_of_le <| le_of_not_lt hx₀
  rcases le_or_lt x 1 with hxπ | hxπ
  case inl =>
    exact pow_lt_pow_left (sin_lt hx₀)
      (sin_nonneg_of_nonneg_of_le_pi hx₀.le (by linarith [two_le_pi])) (by simp)
  case inr =>
    exact (sin_sq_le_one _).trans_lt (by rwa [one_lt_sq_iff hx₀.le])

lemma sin_sq_le_sq : sin x ^ 2 ≤ x ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  case inl => simp
  case inr => exact (sin_sq_lt_sq hx).le

lemma abs_sin_lt_abs (hx : x ≠ 0) : |sin x| < |x| := sq_lt_sq.1 (sin_sq_lt_sq hx)

/- |sin x| ≤ |x| for any real number x-/
variable (x) in
lemma abs_sin_le_abs : |sin x| ≤ |x| := sq_le_sq.1 sin_sq_le_sq

/- If a ≤ b and b < c, then a < c -/
lemma lt_of_le_of_lt {a c: ℝ} (b:ℝ) : a ≤ b → b < c → a < c:= _root_.lt_of_le_of_lt

end CGame
