# Similarity of lower Dedekind real numbers

```agda
module real-numbers.similarity-lower-dedekind-real-numbers where
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

open import real-numbers.lower-dedekind-real-numbers
```

</details>

## Idea

Two [lower Dedekind real numbers](real-numbers.lower-dedekind-real-numbers.md)
are
{{#concept "similar" Disambiguation="lower Dedekind real numbers" Agda=sim-lower-ℝ}}
if their cuts are similar. The similarity relation on lower Dedekind real
numbers extends the [equality](foundation-core.identity-types.md) relation to
lower Dedekind real numbers of differing universe levels.

## Definition

```agda
opaque
  sim-prop-lower-ℝ : {l1 l2 : Level} → lower-ℝ l1 → lower-ℝ l2 → Prop (l1 ⊔ l2)
  sim-prop-lower-ℝ x y = sim-prop-subtype (cut-lower-ℝ x) (cut-lower-ℝ y)

  sim-lower-ℝ : {l1 l2 : Level} → lower-ℝ l1 → lower-ℝ l2 → UU (l1 ⊔ l2)
  sim-lower-ℝ x y = type-Prop (sim-prop-lower-ℝ x y)

infix 6 _~lower-ℝ_
_~lower-ℝ_ : {l1 l2 : Level} → lower-ℝ l1 → lower-ℝ l2 → UU (l1 ⊔ l2)
_~lower-ℝ_ = sim-lower-ℝ
```

## Properties

### Reflexivity

```agda
opaque
  unfolding sim-lower-ℝ

  refl-sim-lower-ℝ : {l : Level} → (x : lower-ℝ l) → x ~lower-ℝ x
  refl-sim-lower-ℝ x = refl-sim-subtype (cut-lower-ℝ x)

  sim-eq-lower-ℝ : {l : Level} → {x y : lower-ℝ l} → x ＝ y → x ~lower-ℝ y
  sim-eq-lower-ℝ {_} {x} {y} x=y = tr (sim-lower-ℝ x) x=y (refl-sim-lower-ℝ x)
```

### Symmetry

```agda
opaque
  unfolding sim-lower-ℝ

  symmetric-sim-lower-ℝ :
    {l1 l2 : Level} → {x : lower-ℝ l1} {y : lower-ℝ l2} →
    x ~lower-ℝ y → y ~lower-ℝ x
  symmetric-sim-lower-ℝ {x = x} {y = y} =
    symmetric-sim-subtype (cut-lower-ℝ x) (cut-lower-ℝ y)
```

### Transitivity

```agda
opaque
  unfolding sim-lower-ℝ

  transitive-sim-lower-ℝ :
    {l1 l2 l3 : Level} →
    (x : lower-ℝ l1) (y : lower-ℝ l2) (z : lower-ℝ l3) →
    y ~lower-ℝ z → x ~lower-ℝ y → x ~lower-ℝ z
  transitive-sim-lower-ℝ x y z =
    transitive-sim-subtype (cut-lower-ℝ x) (cut-lower-ℝ y) (cut-lower-ℝ z)
```

### Similar real numbers in the same universe are equal

```agda
opaque
  unfolding sim-lower-ℝ

  eq-sim-lower-ℝ : {l : Level} → {x y : lower-ℝ l} → x ~lower-ℝ y → x ＝ y
  eq-sim-lower-ℝ {x = x} {y = y} H =
    eq-eq-cut-lower-ℝ x y (eq-sim-subtype _ _ H)
```
