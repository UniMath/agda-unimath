# Similarity of upper Dedekind real numbers

```agda
module real-numbers.similarity-upper-dedekind-real-numbers where
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

open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

Two [upper Dedekind real numbers](real-numbers.upper-dedekind-real-numbers.md)
are
{{#concept "similar" Disambiguation="upper Dedekind real numbers" Agda=sim-upper-ℝ}}
if their cuts are similar. The similarity relation on upper Dedekind real
numbers extends the [equality](foundation-core.identity-types.md) relation to
upper Dedekind real numbers of differing universe levels.

## Definition

```agda
opaque
  sim-prop-upper-ℝ : {l1 l2 : Level} → upper-ℝ l1 → upper-ℝ l2 → Prop (l1 ⊔ l2)
  sim-prop-upper-ℝ x y = sim-prop-subtype (cut-upper-ℝ x) (cut-upper-ℝ y)

  sim-upper-ℝ : {l1 l2 : Level} → upper-ℝ l1 → upper-ℝ l2 → UU (l1 ⊔ l2)
  sim-upper-ℝ x y = type-Prop (sim-prop-upper-ℝ x y)

infix 6 _~upper-ℝ_
_~upper-ℝ_ : {l1 l2 : Level} → upper-ℝ l1 → upper-ℝ l2 → UU (l1 ⊔ l2)
_~upper-ℝ_ = sim-upper-ℝ
```

## Properties

### Reflexivity

```agda
opaque
  unfolding sim-upper-ℝ

  refl-sim-upper-ℝ : {l : Level} → (x : upper-ℝ l) → x ~upper-ℝ x
  refl-sim-upper-ℝ x = refl-sim-subtype (cut-upper-ℝ x)

  sim-eq-upper-ℝ : {l : Level} → {x y : upper-ℝ l} → x ＝ y → x ~upper-ℝ y
  sim-eq-upper-ℝ {_} {x} {y} x=y = tr (sim-upper-ℝ x) x=y (refl-sim-upper-ℝ x)
```

### Symmetry

```agda
opaque
  unfolding sim-upper-ℝ

  symmetric-sim-upper-ℝ :
    {l1 l2 : Level} → {x : upper-ℝ l1} {y : upper-ℝ l2} →
    x ~upper-ℝ y → y ~upper-ℝ x
  symmetric-sim-upper-ℝ {x = x} {y = y} =
    symmetric-sim-subtype (cut-upper-ℝ x) (cut-upper-ℝ y)
```

### Transitivity

```agda
opaque
  unfolding sim-upper-ℝ

  transitive-sim-upper-ℝ :
    {l1 l2 l3 : Level} →
    (x : upper-ℝ l1) (y : upper-ℝ l2) (z : upper-ℝ l3) →
    y ~upper-ℝ z → x ~upper-ℝ y → x ~upper-ℝ z
  transitive-sim-upper-ℝ x y z =
    transitive-sim-subtype (cut-upper-ℝ x) (cut-upper-ℝ y) (cut-upper-ℝ z)
```

### Similar real numbers in the same universe are equal

```agda
opaque
  unfolding sim-upper-ℝ

  eq-sim-upper-ℝ : {l : Level} → {x y : upper-ℝ l} → x ~upper-ℝ y → x ＝ y
  eq-sim-upper-ℝ {x = x} {y = y} H =
    eq-eq-cut-upper-ℝ x y (eq-sim-subtype _ _ H)
```
