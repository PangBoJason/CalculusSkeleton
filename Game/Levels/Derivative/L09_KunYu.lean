import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
import Game.Metadata
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


World "Derivative"

Level 9

Title "The derivative of sin(sin(sin (x)))"



lemma sinsinx_differentiable (x : ℝ) : DifferentiableAt ℝ (fun x => Real.sin ( Real.sin x )) x := by sorry

Statement (x : ℝ) : deriv (fun x => Real.sin ( Real.sin ( Real.sin x ) ) ) (x : ℝ) =
 Real.cos x * Real.cos ( Real.sin x ) * Real.cos ( Real.sin ( Real.sin x ) ) := by
 Hint "This is an application of 'Composite Function Derivative', firstly you need to let lean figure out what is the composite function which means you need to set sin(sinx) as function g"
 Hint "Try tactic: set g := fun x => ..."
 set g := fun x => Real.sin ( Real.sin x )
 Hint "Try to rewrite the question"
 have : (fun x => Real.sin ( Real.sin ( Real.sin x ) )) = Real.sin ∘ g := rfl
 Hint "Try rw[] to apply the assumption"
 rw[this]
 Hint "Now we can use the tactic: deriv.comp"
 rw[deriv.comp]
 Hint "Solve the derivetive by the tactic deriv_.."
 rw[Real.deriv_sin]
 Hint "To solve the derivetive of sin(sinx), we need to have some assumptions by the tactic 'have' and we can prove it in the same way of this question"
 have h : deriv (fun x => Real.sin ( Real.sin x )) (x : ℝ) = Real.cos x * Real.cos (Real.sin x) := by
  set g := fun x => Real.sin x
  have : (fun x => Real.sin (Real.sin x)) = Real.sin ∘ g := rfl
  rw[this]
  rw[deriv.comp]
  rw[Real.deriv_sin]
  rw[mul_comm]
  Hint "Now we only need to apply Real.differentiableAt_sin"
  exact Real.differentiableAt_sin
  exact Real.differentiableAt_sin
 Hint "apply the rewrite tactic"
 rw[h]
 Hint "Try mul_comm"
 rw[mul_comm]
 Hint "Solve the differentiable question by tactic: Real.differentiableAt_sin"
 exact Real.differentiableAt_sin
 Hint "Suppose that we already have the sinsinx_differentiable"
 exact sinsinx_differentiable x







-- The derivative of sin(sin(sin (x)))
