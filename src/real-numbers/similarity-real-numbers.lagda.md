# Similarity of real numbers

```agda
module real-numbers.similarity-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.similarity-of-elements-large-posets

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
```

</details>

## Idea

Two [Dedekind real numbers](real-numbers.dedekind-real-numbers.md) are
{{#concept "similar" Disambiguation="Dedekind real numbers" Agda=sim-ℝ}} if they
are [less than or equal](real-numbers.inequality-real-numbers.md) to each other.
The similarity relation on real numbers extends the
[equality](foundation-core.identity-types.md) relation to real numbers of
differing universe levels.

## Definition

```agda
sim-prop-ℝ : {l1 l2 : Level} → ℝ l1 → ℝ l2 → Prop (l1 ⊔ l2)
sim-prop-ℝ = sim-prop-Large-Poset ℝ-Large-Poset

sim-ℝ : {l1 l2 : Level} → ℝ l1 → ℝ l2 → UU (l1 ⊔ l2)
sim-ℝ x y = type-Prop (sim-prop-ℝ x y)
```

## Properties

### Similarity in the real numbers is equivalent to similarity of lower cuts

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  sim-lower-cut-iff-sim-ℝ :
    sim-subtype (lower-cut-ℝ x) (lower-cut-ℝ y) ↔ sim-ℝ x y
  sim-lower-cut-iff-sim-ℝ = id-iff
```

### Similarity in the real numbers is equivalent to similarity of upper cuts

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  sim-upper-cut-iff-sim-ℝ :
    sim-subtype (upper-cut-ℝ x) (upper-cut-ℝ y) ↔ sim-ℝ x y
  pr1 (pr1 sim-upper-cut-iff-sim-ℝ (ux⊆uy , uy⊆ux)) =
    backward-implication (leq-iff-ℝ' x y) uy⊆ux
  pr2 (pr1 sim-upper-cut-iff-sim-ℝ (ux⊆uy , uy⊆ux)) =
    backward-implication (leq-iff-ℝ' y x) ux⊆uy
  pr1 (pr2 sim-upper-cut-iff-sim-ℝ (lx⊆ly , ly⊆lx)) =
    forward-implication (leq-iff-ℝ' y x) ly⊆lx
  pr2 (pr2 sim-upper-cut-iff-sim-ℝ (lx⊆ly , ly⊆lx)) =
    forward-implication (leq-iff-ℝ' x y) lx⊆ly
```

### Reflexivity

```agda
refl-sim-ℝ : {l : Level} → (x : ℝ l) → sim-ℝ x x
refl-sim-ℝ = refl-sim-Large-Poset ℝ-Large-Poset
```

### Transitivity

```agda
transitive-sim-ℝ :
  {l1 l2 l3 : Level} →
  (x : ℝ l1) →
  (y : ℝ l2) →
  (z : ℝ l3) →
  sim-ℝ y z →
  sim-ℝ x y →
  sim-ℝ x z
transitive-sim-ℝ = transitive-sim-Large-Poset ℝ-Large-Poset
```

### Antisymmetry at the same universe level

```agda
antisymmetric-sim-ℝ : {l : Level} → (x y : ℝ l) → sim-ℝ x y → x ＝ y
antisymmetric-sim-ℝ = eq-sim-Large-Poset ℝ-Large-Poset
```
### A rational real is similar to the canonical projection of its rational

```agda
sim-rational-ℝ :
  {l : Level} →
  (x : Rational-ℝ l) →
  sim-rational-ℝ (real-rational-ℝ x) (real-ℚ (rational-rational-ℝ x))
sim-rational-ℝ (x , q , x-is-q) = ?
```
