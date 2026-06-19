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

/-! ## 7. Universal Approximation (Continuous Morphism and Address Space) -/

/-
We define the topological representation space, which lifts the category-theoretic
terminality (`morphism_uniqueness`) to the continuous setting. 

Rather than treating the input/output projections (encode/readout) as fixed global
axioms, they are existentially quantified as part of the configuration space (RawAddress),
matching the standard Cybenko/Hornik universal approximation theorem (Option A).

To represent the continuous mapping uniquely, the parameter space is quotiented modulo
observational (functional) equivalence, mirroring the discrete `InvariantLayer`.

**Axiom inventory** (all intentional — see ADR-003):
  activatedUpdate, ISAR_UAT.
-/

/-- A nonlinear activation function: continuous real functions ℝ → ℝ. -/
abbrev Activation := C(ℝ, ℝ)

/-- Horner's method to evaluate a polynomial represented as a list of real coefficients. -/
def evalPoly (coeffs : List ℝ) (x : ℝ) : ℝ :=
  coeffs.foldr (fun coef acc => coef + x * acc) 0

/-- Predicate: σ is non-polynomial (necessary condition for representation). -/
def Activation.nonPolynomial (σ : Activation) : Prop :=
  ∀ coeffs : List ℝ, (σ : ℝ → ℝ) ≠ evalPoly coeffs

/--
Grid state: N cells, each with a 4-dimensional real state vector.
`EuclideanSpace ℝ (Fin (4 * N))` is a concrete Mathlib type carrying
`NormedAddCommGroup`, `InnerProductSpace ℝ`, and all analytic structure.
-/
abbrev GridState (N : Nat) := EuclideanSpace ℝ (Fin (4 * N))

/-- T-step ISAR update with alternating activation, returning a continuous map. -/
axiom activatedUpdate (σ : Activation) (N T : Nat) (θ : Fin T → Fin 4 → ℝ) :
  C(GridState N, GridState N)

/--
`RawAddress`: the concrete configuration space representing all finite-grid,
finite-time neural representations of the ISAR update.
Contains the grid size N, time steps T, parameter sequence θ, and the bundled
continuous encoder and readout maps.
-/
def RawAddress (d k : Nat) : Type :=
  Σ (N T : Nat),
    (Fin T → Fin 4 → ℝ) ×
    C(EuclideanSpace ℝ (Fin d), GridState N) ×
    C(GridState N, EuclideanSpace ℝ (Fin k))

/--
The realization map mapping a raw parameter trajectory to a continuous function.
Computes the composition: readout ∘ activatedUpdate ∘ encode.
-/
noncomputable def realizeRaw (d k : Nat) (σ : Activation) (θ : RawAddress d k) :
    C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin k)) :=
  let N := θ.1
  let T := θ.2.1
  let θ_seq := θ.2.2.1
  let encode := θ.2.2.2.1
  let readout := θ.2.2.2.2
  readout.comp ((activatedUpdate σ N T θ_seq).comp encode)

/--
Two raw addresses are observationally/functionally equivalent if they realize
the same continuous function.
-/
def AddressEq (d k : Nat) (σ : Activation) (θ₁ θ₂ : RawAddress d k) : Prop :=
  realizeRaw d k σ θ₁ = realizeRaw d k σ θ₂

/-- The setoid defining the functional equivalence relation on RawAddress. -/
noncomputable def addressSetoid (d k : Nat) (σ : Activation) : Setoid (RawAddress d k) where
  r := AddressEq d k σ
  iseqv := {
    refl  := fun _ => rfl
    symm  := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }

/--
`KernelAddress`: the address space defined as the quotient of RawAddress modulo
observational/functional equivalence. This is the exact continuous counterpart to
the discrete `InvariantLayer`.
-/
def KernelAddress (d k : Nat) (σ : Activation) : Type :=
  Quotient (addressSetoid d k σ)

/--
The well-defined continuous realization of a quotiented `KernelAddress`.
Derived via `Quotient.lift` from `realizeRaw`.
-/
noncomputable def continuousRealization (d k : Nat) (σ : Activation) (q : KernelAddress d k σ) :
    C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin k)) :=
  Quotient.lift (fun θ => realizeRaw d k σ θ) (by
    intro θ₁ θ₂ h
    exact h
  ) q

/--
**ISAR Universal Approximation Theorem.**

For any continuous function f : ℝᵈ → ℝᵏ, a non-polynomial activation σ,
and a compact domain K ⊆ ℝᵈ, the finite-grid iterated ISAR update can
approximate f uniformly on K to arbitrary precision ε > 0.

This is the standard Cybenko/Hornik universal approximation theorem applied to the
ISAR configuration space (RawAddress).
-/
axiom ISAR_UAT
    (d k : Nat)
    (K : Set (EuclideanSpace ℝ (Fin d)))
    (_ : IsCompact K)
    (f : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin k)))
    (σ : Activation)
    (_ : Activation.nonPolynomial σ)
    (ε : ℝ) (_ : 0 < ε) :
    ∃ θ : RawAddress d k,
      ∀ x ∈ K,
        ‖realizeRaw d k σ θ x - f x‖ < ε

/--
**Corollary: Logical and Statistical Universality.**

The ISAR kernel simultaneously achieves:
1. **Logical universality** (proved, zero extra axioms):
   `morphism_uniqueness` — every admissible formal rewriting system embeds uniquely
   into ISAR_Kernel.
2. **Statistical universality** (analytic UAT axiom `ISAR_UAT`):
   every continuous function ℝᵈ → ℝᵏ is approximable by the iterated ISAR update
   on any compact subset K to arbitrary precision ε > 0.
-/
theorem ISAR_logical_and_statistical_universality :
    (∀ (K : Kernel) (f : KernelHom K ISAR_Kernel) (c : K.Carrier),
        OperEq (f.hom c) (K.decode c)) ∧
    (∀ (d k : Nat) (K : Set (EuclideanSpace ℝ (Fin d))) (_ : IsCompact K)
        (f : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin k)))
        (σ : Activation) (_ : Activation.nonPolynomial σ) (ε : ℝ) (_ : 0 < ε),
        ∃ θ : RawAddress d k,
          ∀ x ∈ K,
            ‖realizeRaw d k σ θ x - f x‖ < ε) :=
  ⟨fun K f c => morphism_uniqueness K f c,
   fun d k K hK f σ σ_np ε hε => ISAR_UAT d k K hK f σ σ_np ε hε⟩

end ISAR
