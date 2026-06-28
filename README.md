# ISAR: Invariant Kernel for Closed Computational Dialects

ISAR is a Lean 4 formalization of a minimal combinatory substrate whose operational quotient — the **Invariant Layer** — is the terminal object in the category of closed computational dialects. Lambda calculus, term rewriting systems, stack VM bytecode, hereditarily finite sets, and linear interaction nets all factor uniquely through this quotient via structure-preserving morphisms. All 22 modules are machine-checked and **sorry-free**.

The core factorization pattern is:
$$\text{Encoder} \to \text{Kernel} \to \text{Quotient (InvariantLayer)} \to \text{Decoder}$$
Different formalisms are precisely the decoders; the quotient is the invariant substrate shared by all.

---

## Summary of Verified Modules

### Phase 1: Core Calculus

1. **[ISAR.lean](ISAR.lean)** — Syntax, rewrite rules, confluence, unique normal forms for `ISKTerm`, and basis completeness (derives $S$ from $I, K, W, C, B$).

2. **[InvariantLayer.lean](InvariantLayer.lean)** — `OperEq` joinability quotient, `app_congruence`, `canonical_rep` (computable via `cd_loop` with `@[implemented_by]`), `cd_size_lt_IK` termination proof, fuel-based normalization loop `cd_loop_fuel`, and `cd_loop_fuel_quotient_eq`.

3. **[LambdaFragment.lean](LambdaFragment.lean)** — de Bruijn `LTerm`, bracket abstraction `abstract0`, compiler `compile`, simulation: `compile_simulates_step` and `compile_simulates_red`.

4. **[TensorSemantics.lean](TensorSemantics.lean)** — `denot_sound`, `lambda_denot_sound`, `toExtTensor_app` homomorphism, adequacy: `adequacy_family` separating $I$, $K$, $K_2$.

5. **[KernelCategory.lean](KernelCategory.lean)** — `Kernel` structure, `ISAR_Kernel` terminal object, `ComputableISAR_Kernel`, `morphism_uniqueness` (terminality).

---

### Phase 2: Set-Theoretic Interpretation

6. **[HFSet.lean](HFSet.lean)** — Inductive `HF` type, Ackermann `toNat` bijection, membership, extensional equality, set axioms.

7. **[HFSetEncoding.lean](HFSetEncoding.lean)** — `HF_encode` / `decode_term` bijection between `InvariantLayer` and `HF`, coherence equations.

8. **[HFSetSemantics.lean](HFSetSemantics.lean)** — Lifts set constructors to `InvariantLayer`; proves `HF_encode` is a homomorphism.

9. **[ZFCInterpretation.lean](ZFCInterpretation.lean)** — `HF_Kernel` instance, interpretation theorem, unique factorization through `ISAR_Kernel`.

---

### Phase 3: Dialect Views & View Pluralism

10. **[DialectKernel.lean](DialectKernel.lean)** — `Dialect` structure: encode, decode, eval, preservation law.

11. **[ViewIndependence.lean](ViewIndependence.lean)** — `ObservationalIsomorphism`, **No Preferred Syntax Theorem** (`no_preferred_syntax`), reflexivity/symmetry/transitivity.

12. **[ReverseRosetta.lean](ReverseRosetta.lean)** — `closure_preserved_under_reachability` (forward invariance), `referentially_open_requires_anchor` (referential openness).

13. **[TRSView.lean](TRSView.lean)** — `TTerm` SKI dialect, `trs_encode`, `decode_raw`, `TRS_Dialect`.

14. **[BytecodeView.lean](BytecodeView.lean)** — Stack VM (`push_I`, `push_K`, `push_S`, `app`), `run`, `compile_decompile` identity, `Bytecode_Dialect`.

15. **[QuantityKernel.lean](QuantityKernel.lean)** — 4-layer quantity algebra, `QuantityKernel : Kernel`, `InvariantLayer.add` preserves arithmetic addition.

16. **[ViewUnification.lean](ViewUnification.lean)** — `AdmissibleDialect`, `KernelIsomorphism`, **Universal Factorization Theorem** (`universal_factorization_theorem`).

17. **[Futamura.lean](Futamura.lean)** — Substitution, partial evaluation, **First/Second/Third Futamura Projections** constructively proved.

---

### Phase 4: Linear Duplication, Optimal Kernels & Matrix Geometry

18. **[ISARMatrices.lean](ISARMatrices.lean)** — $4 \times 4$ integer matrices, $I^2 = I$ (idempotency), $(IRAS)^2 = 0$ (nilpotency), gauge equivalence $P K_1 P^{-1} = K_2$.

19. **[InvariantLayer.lean](InvariantLayer.lean)** — `LinearIKTerm`, `dupCount`, `cd_size_lt_LinearIK`, `sufficient_fuel` certificate and `sufficient_fuel_correct`.

20. **[KernelCategory.lean](KernelCategory.lean)** — `ComputableISAR_Kernel_Optimal` with optimal fuel certificate.

---

### Phase 5: Metric Completion & Continuous Semantics

21. **[ISARApproximation.lean](ISARApproximation.lean)** — Pseudo-metric on `KernelAddress d k σ` (supremum norm), metric completion `KernelAddressLimit`, dense embedding extension, Universal Approximation Theorem (Leshno 1993), and physical system attractor embeddings (Lorenz, Gray-Scott, Ising).

---

## Connection to HVM2 & Linear Interaction Nets

| `LinearIKTerm` Property | HVM2 / Interaction Net Concept |
|:---|:---|
| `LinearIKTerm` predicate | Linearity constraint (no nested duplicator nodes) |
| `dupCount t = 0` | Pure linear fragment, $O(1)$ per redex |
| `dup` operator | Duplicator / fan node |
| Complete development `cd` | Parallel reduction layer |
| `cd_size_lt_LinearIK` | Size decrease, termination |
| `sufficient_fuel_correct` | Max interaction bound |
| Relational $U$-table contraction | Port linking |

---

## Local Build

```bash
git clone https://github.com/cypoe/isar-proofs.git
cd isar-proofs
lake build
```

Blueprint (PDF + HTML):

```bash
cd blueprint
latexmk -pdf src/print.tex          # twice to resolve cross-refs
plastex -c src/plastex.cfg src/web.tex
```

Or via Docker (no local LaTeX install):

```powershell
docker run --rm -v "${PWD}:/doc" -w /doc/blueprint/src texlive/texlive xelatex print.tex
```

Validate all 71 blueprint declarations against the Lean source:

```bash
lake exe checkdecls blueprint/lean_decls
```

---

## Narratives

- Phase 1: [story.md](story.md)
- Phase 2: [hf_story.md](hf_story.md)
- Phase 3: [reverse_rosetta_story.md](reverse_rosetta_story.md)
