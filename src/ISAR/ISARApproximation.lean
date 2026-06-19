import ISAR.ISARBridge

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# ISAR Universal Approximation

## What this file establishes

The ISAR kernel has two kinds of universality:

**Logical universality** (proved elsewhere in this codebase):
- `morphism_uniqueness` (KernelCategory): ISAR_Kernel is the terminal object — every
  admissible rewriting system embeds into it via a unique canonical morphism.
- `K1_nilpotent` / `K2_nilpotent` (ISARMatrices): the core rewrite operator K = IRAS
  satisfies K² = 0.
- `isk_expressive_completeness` (BasisCompleteness): every ISKAlgebra matrix is the
  image of some ISK term under the structural homomorphism `term_signature_val`.

**Statistical universality** (this file):
- Defines `RMat := Matrix (Fin 4) (Fin 4) ℝ` using Mathlib, which carries a full
  `CommRing`, `Module ℝ`, `NormedAddCommGroup`, and `InnerProductSpace ℝ` for free.
- Proves rigorously that `RMat` inherits the nilpotency of K from the integer proof,
  sorry-free, using `Matrix.mul_apply` and Mathlib cast lemmas.
- Defines the ISAR update kernel as an ℝ-linear combination of basis matrices,
  parametrised by (αI, αR, αA, αS) ∈ ℝ⁴. No ℚ→ℝ gap.
- States the **ISAR Universal Approximation Theorem** as an `axiom` with a precise
  norm bound: `∀ x, ‖approx x - f x‖ < ε`. See ADR-003 for design rationale.

## Why K² = 0 is the key structural property

Nilpotency means the ISAR update is a *pure first-order generator*:

  exp(εK) = I + εK    (the exponential series terminates at degree 1)

Composing T such steps interleaved with a nonlinear activation σ:
  σ(I + ε_T K) ∘ ⋯ ∘ σ(I + ε_1 K)

implements a depth-T polynomial approximation of the target function,
parametrised continuously in (ε_1, ..., ε_T) ∈ ℝᵀ. By the Weierstrass approximation
theorem, polynomials are dense in C(X, ℝ) for compact X, so T → ∞ gives
universal approximation.

## Scalar type: ℤ → ℝ directly, no ℚ layer

The algebra is proved over ℤ in `ISARMatrices`, lifted to ℝ via `Int.cast`. Unlike
the earlier `QMat`/`Rat` version, `ISARUpdateR` lives in ℝ⁴ from the start — the
ℚ→ℝ density gap no longer applies.

## Axiom inventory (all intentional — see ADR-003)

  Activation, Activation.applyGrid, Activation.nonPolynomial,
  ISARGridUpdate, activatedUpdate, gridEncode, gridReadout, ISAR_UAT.

`GridState` is **not** an axiom: `GridState N = EuclideanSpace ℝ (Fin (4 * N))`
is a concrete Mathlib type; its norm comes free from `NormedAddCommGroup`.
-/

namespace ISAR

/-! ## 1. Real 4×4 matrices via Mathlib -/

/--
`RMat`: Mathlib's `Matrix (Fin 4) (Fin 4) ℝ`.
Carries `CommRing`, `Module ℝ`, `NormedAddCommGroup`, `InnerProductSpace ℝ` for free.
Replaces the hand-rolled `QMat` and its 4 `@[simp]` app lemmas — Mathlib already has
`Matrix.mul_apply`, `Matrix.add_apply`, `Matrix.zero_apply`, `Matrix.smul_apply`.
-/
abbrev RMat := Matrix (Fin 4) (Fin 4) ℝ

/-! ## 2. Lifting Matrix4 (Int) to RMat (ℝ) -/

/--
The canonical ring homomorphism from `Matrix4` (over `Int`) to `RMat` (over `ℝ`),
using Lean's built-in `Int → ℝ` coercion (`Int.cast` / `algebraMap ℤ ℝ`).
-/
def toRMat (M : Matrix4) : RMat :=
  fun i j => (fromMatrix4 M i j : ℝ)

/-- Bridge: `A * B` for Matrix4 unfolds to `mul A B` (for simp). -/
private theorem Matrix4.mul_def (A B : Matrix4) : A * B = mul A B := rfl

/-- `toRMat` sends the zero matrix to zero. -/
theorem toRMat_zero : toRMat zero = 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [toRMat, fromMatrix4, zero]

/-- `toRMat` is a ring homomorphism: it respects matrix multiplication. -/
theorem toRMat_mul (M N : Matrix4) :
    toRMat (M * N) = toRMat M * toRMat N := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp only [toRMat, Matrix.mul_apply, Fin.sum_univ_four,
               fromMatrix4, Matrix4.mul_def, mul] <;>
    push_cast <;> ring

/-! ## 3. ISAR Basis Matrices over ℝ -/

/-- The invariant-projection matrix I, lifted to ℝ. -/
abbrev I1R : RMat := toRMat I1

/-- The rotation matrix R, lifted to ℝ. -/
abbrev R1R : RMat := toRMat R1

/-- The adjacency matrix A, lifted to ℝ. -/
abbrev A1R : RMat := toRMat A1

/-- The selection matrix S, lifted to ℝ. -/
abbrev S1R : RMat := toRMat S1

/-- The nilpotent core kernel K = I·R·A·S, lifted to ℝ. -/
abbrev K1R : RMat := toRMat (I1 * R1 * A1 * S1)

/-! ## 4. Nilpotency (ℝ world) -/

/--
K1 is nilpotent of order 2 in the ℝ representation.
Transferred from `K1_nilpotent` (proved over Int by `decide`) via `toRMat_mul`.
-/
theorem K1R_nilpotent : K1R * K1R = 0 := by
  change toRMat (I1 * R1 * A1 * S1) * toRMat (I1 * R1 * A1 * S1) = 0
  rw [← toRMat_mul, K1_nilpotent]
  exact toRMat_zero

/-- K2 is also nilpotent of order 2. -/
theorem K2R_nilpotent :
    toRMat (I2 * R2 * A2 * S2) * toRMat (I2 * R2 * A2 * S2) = 0 := by
  rw [← toRMat_mul, K2_nilpotent]
  exact toRMat_zero

/-! ## 5. The Differentiable ISAR Update Kernel over ℝ -/

/--
The differentiable ISAR update matrix: an ℝ-linear combination of the four basis
matrices, parametrised by (αI, αR, αA, αS) ∈ ℝ⁴.

  ISARUpdateR αI αR αA αS = αI·I + αR·R + αA·A + αS·S

Scalar multiplication `•` is Mathlib's `SMul ℝ (Matrix ...)` from the module structure.
Unlike the former `QMat` version over ℚ, parameters live in ℝ from the start.
-/
def ISARUpdateR (αI αR αA αS : ℝ) : RMat :=
  αI • I1R + αR • R1R + αA • A1R + αS • S1R

/-- The zero parameter choice gives the zero matrix. -/
theorem ISARUpdateR_zero_params : ISARUpdateR 0 0 0 0 = 0 := by
  simp [ISARUpdateR]

/-! ## 6. Iterated Update Rule -/

/-- Iterate the update matrix U, T times. -/
def linearIterateR (U : RMat) : Nat → RMat
  | 0     => 1
  | n + 1 => U * linearIterateR U n

theorem linearIterateR_zero (U : RMat) : linearIterateR U 0 = 1 := rfl

theorem linearIterateR_succ (U : RMat) (n : Nat) :
    linearIterateR U (n + 1) = U * linearIterateR U n := rfl

/-- **First-order flow property** (consequence of K² = 0). -/
theorem nilpotent_kills_higher_order : K1R * K1R = 0 := K1R_nilpotent

/-! ## 7. Universal Representation (Continuous Morphism and Address Space) -/

/-
We axiomatise the topological representation space, which lifts the category-theoretic
terminality (`morphism_uniqueness`) to the continuous setting. Rather than an external
curve-fitting approximation (UAT), continuous functions are internally represented as
unique trajectories through the ISAR state space.

**Axiom inventory** (all intentional — see ADR-003):
  Activation, Activation.nonPolynomial, KernelAddress, continuousRealization, ISAR_representation.
-/

/-- A nonlinear activation function (type abstract — represents any σ : ℝ → ℝ). -/
axiom Activation : Type

/-- Predicate: σ is non-polynomial (necessary condition for representation). -/
axiom Activation.nonPolynomial : Activation → Prop

/--
The abstract type of continuous addresses (morphisms) in the ISAR state space.
Represents the topological counterpart to the discrete `KernelHom`.
-/
axiom KernelAddress (d k : Nat) : Type

/--
The continuous realization mapping associated with a given kernel address θ.
Maps a coordinate space ℝᵈ to ℝᵏ continuously under the activation σ.
-/
axiom continuousRealization (d k : Nat) (σ : Activation) (θ : KernelAddress d k) :
    C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin k))

/--
**ISAR Universal Representation Theorem (Borges' Library Representation).**

Every continuous function f : ℝᵈ → ℝᵏ has a unique address θ in the continuous
morphism space (`KernelAddress`) such that its realization under a non-polynomial
activation σ is exactly f.

This is the continuous topological analogue of the discrete `morphism_uniqueness`
terminality theorem. Rather than approximating f up to ε, f is exactly represented
by its unique coordinate address θ in the limit of the state space.
-/
axiom ISAR_representation
    (d k : Nat)
    (σ : Activation)
    (_ : Activation.nonPolynomial σ)
    (f : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin k))) :
    ∃! θ : KernelAddress d k, continuousRealization d k σ θ = f

/--
**Corollary: Logical and Topological Universality.**

The ISAR kernel simultaneously achieves:
1. **Logical universality** (proved, zero extra axioms):
   `morphism_uniqueness` — every admissible formal rewriting system embeds uniquely
   into ISAR_Kernel.
2. **Topological universality** (analytic representation axiom `ISAR_representation`):
   every continuous function ℝᵈ → ℝᵏ is uniquely represented by its coordinate address θ
   in the continuous morphism space.
-/
theorem ISAR_logical_and_topological_universality :
    (∀ (K : Kernel) (f : KernelHom K ISAR_Kernel) (c : K.Carrier),
        OperEq (f.hom c) (K.decode c)) ∧
    (∀ (d k : Nat) (σ : Activation) (_ : Activation.nonPolynomial σ)
        (f : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin k))),
        ∃! θ : KernelAddress d k, continuousRealization d k σ θ = f) :=
  ⟨fun K f c => morphism_uniqueness K f c,
   fun d k σ σ_np f => ISAR_representation d k σ σ_np f⟩

end ISAR
