# Similarity of nonnegative real numbers

```agda
module real-numbers.similarity-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.nonnegative-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

Two [nonnegative](real-numbers.nonnegative-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) are
{{#concept "similar" Disambiguation="nonnegative real numbers" Agda=sim-ℝ⁰⁺}} if
they are [similar](real-numbers.similarity-real-numbers.md) as real numbers.

## Definition

### Similarity of nonnegative real numbers

```agda
module _
  {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2)
  where

  sim-prop-ℝ⁰⁺ : Prop (l1 ⊔ l2)
  sim-prop-ℝ⁰⁺ = sim-prop-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y)

  sim-ℝ⁰⁺ : UU (l1 ⊔ l2)
  sim-ℝ⁰⁺ = sim-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y)

infix 6 _~ℝ⁰⁺_
_~ℝ⁰⁺_ : {l1 l2 : Level} → ℝ⁰⁺ l1 → ℝ⁰⁺ l2 → UU (l1 ⊔ l2)
_~ℝ⁰⁺_ = sim-ℝ⁰⁺

sim-zero-prop-ℝ⁰⁺ : {l : Level} → ℝ⁰⁺ l → Prop l
sim-zero-prop-ℝ⁰⁺ = sim-prop-ℝ⁰⁺ zero-ℝ⁰⁺

sim-zero-ℝ⁰⁺ : {l : Level} → ℝ⁰⁺ l → UU l
sim-zero-ℝ⁰⁺ = sim-ℝ⁰⁺ zero-ℝ⁰⁺

eq-sim-ℝ⁰⁺ : {l : Level} (x y : ℝ⁰⁺ l) → sim-ℝ⁰⁺ x y → x ＝ y
eq-sim-ℝ⁰⁺ x y x~y = eq-ℝ⁰⁺ x y (eq-sim-ℝ {x = real-ℝ⁰⁺ x} {y = real-ℝ⁰⁺ y} x~y)
```

#### Similarity is symmetric

```agda
abstract
  symmetric-sim-ℝ⁰⁺ :
    {l1 l2 : Level} → (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) → x ~ℝ⁰⁺ y → y ~ℝ⁰⁺ x
  symmetric-sim-ℝ⁰⁺ _ _ = symmetric-sim-ℝ
```
