# Similarity of real numbers

```agda
module real-numbers.similarity-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.powersets
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.similarity-of-elements-large-posets

open import real-numbers.dedekind-real-numbers
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
sim-prop-ℝ x y = sim-prop-subtype (lower-cut-ℝ x) (lower-cut-ℝ y)

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
  pr1 sim-upper-cut-iff-sim-ℝ = sim-lower-cut-sim-upper-cut-ℝ x y
  pr2 sim-upper-cut-iff-sim-ℝ = sim-upper-cut-sim-lower-cut-ℝ x y
```

### Reflexivity

```agda
refl-sim-ℝ : {l : Level} → (x : ℝ l) → sim-ℝ x x
refl-sim-ℝ x = refl-sim-subtype (lower-cut-ℝ x)

sim-eq-ℝ : {l : Level} → {x y : ℝ l} → x ＝ y → sim-ℝ x y
sim-eq-ℝ {_} {x} {y} x=y = tr (sim-ℝ x) x=y (refl-sim-ℝ x)
```

### Symmetry

```agda
symmetric-sim-ℝ :
  {l1 l2 : Level} → (x : ℝ l1) (y : ℝ l2) → sim-ℝ x y → sim-ℝ y x
symmetric-sim-ℝ x y = symmetric-sim-subtype (lower-cut-ℝ x) (lower-cut-ℝ y)
```

### Transitivity

```agda
transitive-sim-ℝ :
  {l1 l2 l3 : Level} →
  (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
  sim-ℝ y z → sim-ℝ x y → sim-ℝ x z
transitive-sim-ℝ x y z =
  transitive-sim-subtype (lower-cut-ℝ x) (lower-cut-ℝ y) (lower-cut-ℝ z)
```

### Similar real numbers in the same universe are equal

```agda
eq-sim-ℝ : {l : Level} → (x y : ℝ l) → sim-ℝ x y → x ＝ y
eq-sim-ℝ x y H = eq-eq-lower-cut-ℝ x y (antisymmetric-sim-subtype _ _ H)
```
