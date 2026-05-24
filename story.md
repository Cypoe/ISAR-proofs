# ISAR: A Unified Narrative of the Verified Vertical Stack

This document presents the complete narrative of the ISAR stack, describing the relationship between the representation-free ontological substrate, the operational quotient layer, the symbolic rewrite calculus, and the universal category of semantic views.

---

## 1. The Ontological Substrate (Tensor Space)
At the bottom of the stack lies the **Tensor Space** ($T$): a representation-free ontological substrate.
* **Extensional Equivalence ($\approx_{ext}$)**: Instead of syntactic identity, calculations in Tensor Space are compared via extensional equivalence (`ExtEq`), allowing different concrete implementations to represent the same underlying computation.
* **Structural Carriers**: The substrate is populated by primitive operators including `t_norm`, `t_konst`, `t_dup`, `t_swap`, and `t_comp` (corresponding to combinators $I, K, W, C, B$).
* **Derived $S$ Combinator**: Rather than introducing $S$ as a primitive carrier, we constructively derive it from the structural basis:
  $$ S = B(BW)(C(BB(BBC))I) $$
  and prove that it extensionally satisfies the $S$-combinator beta-reduction rule:
  $$ S \cdot x \cdot y \cdot z \approx_{ext} x \cdot z \cdot (y \cdot z) $$
  This demonstrates that the computational substrate is built purely on structural carriers.

---

## 2. The Invariant Layer (Operational Quotient)
Directly above the substrate is the **Invariant Layer**:
* **Operational Equivalence ($\approx_{op}$)**: Defined as joinability under multi-step reduction in the symbolic calculus. We proved that this forms a rigorous equivalence relation (reflexive, symmetric, and transitive).
* **Quotient Space**: The type `InvariantLayer` is the quotient of symbolic terms modulo operational equivalence.
* **Canonical Representatives**: We proved that for any term possessing a normal form, there exists a well-defined canonical representative in the quotient. This establishes that the invariant layer packages computation up to equivalence, independent of evaluation paths.

---

## 3. The Symbolic ISAR Calculus
The **Symbolic ISAR Calculus** (`ITerm`) is the canonical rewrite presentation of the invariant quotient.
* **Syntactic Rewrite Rules**: Implements one-step reduction (`IStep`) and multi-step reduction (`IRed`).
* **Confluence & Uniqueness**: Proves confluence and uniqueness of normal forms on the symbolic fragment, ensuring that evaluation is deterministic at the quotient level.
* **Conservative Definability**: To prove that the primitive $S$ combinator is not strictly necessary for the rewrite calculus, we proved that reductions in the full system can be simulated in a system using only the derived basis (`IStepBasis`).

---

## 4. The Lambda Compiler & Adequacy
To demonstrate the expressive power of the stack, we compiled the **Untyped Lambda Calculus** (`LTerm`) with de Bruijn indices into the symbolic ISAR calculus:
* **Simulation**: Compilation preserves operational behavior; a beta-reduction step in Lambda Calculus maps to a multi-step reduction in ISAR.
* **Compositionality**: Denotation of compiled terms is a homomorphism with respect to application:
  $$ \text{denot}(\text{compile}(t \cdot u)) \approx_{ext} \text{denot}(\text{compile}(t)) \cdot \text{denot}(\text{compile}(u)) $$
* **Restricted Adequacy (Separation)**: We proved that the tensor semantics distinguishes distinct closed normal forms of the lambda fragment. Specifically, we defined a three-element family:
  1. $I = \lambda x. x$
  2. $K = \lambda x y. x$
  3. $K_2 = \lambda x y z. x$
  and proved that their compiled tensor denotations are pairwise distinct under extensional equality.

---

## 5. Categorical Universality (Terminality of ISAR)
To close the arc, we formalized the **Category of Admissible Semantic Kernels** ($\mathcal{K}$):
* **Objects**: A `Kernel` is a semantic decode view consisting of a carrier, a view map from the fragment, an equivalence relation, and coherence axioms mapping back and forth via a `decode` function.
* **Morphisms**: A `KernelHom` is a function between carrier types that preserves the view mappings and congruence relations.
* **Terminal Object**: The quotient-level ISAR presentation (`ISAR_Kernel`) is proven to be the **terminal object** in this category:
  * We proved the **Uniqueness (Terminality) Theorem**: any structure-preserving morphism from an arbitrary semantic kernel $K$ into `ISAR_Kernel` is observationally equivalent to the canonical decoding morphism.
  * This establishes ISAR as the canonical representation-free semantic presentation of the computational substrate.
