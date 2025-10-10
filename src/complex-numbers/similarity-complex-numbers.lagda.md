# Similarity of complex numbers

```agda
module complex-numbers.similarity-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.similarity-real-numbers
```

</details>

## Idea

Two [complex numbers](complex-numbers.complex-numbers.md) are
{{#concept "similar" Disambiguation="complex numbers" Agda=sim-ℂ}} if their
[real](real-numbers.dedekind-real-numbers.md) and imaginary parts are
[similar](real-numbers.similarity-real-numbers.md).

## Definition

```agda
sim-prop-ℂ : {l1 l2 : Level} → ℂ l1 → ℂ l2 → Prop (l1 ⊔ l2)
sim-prop-ℂ (a , b) (c , d) = sim-prop-ℝ a c ∧ sim-prop-ℝ b d

sim-ℂ : {l1 l2 : Level} → ℂ l1 → ℂ l2 → UU (l1 ⊔ l2)
sim-ℂ a+bi c+di = type-Prop (sim-prop-ℂ a+bi c+di)
```

## Properties

### Similarity is reflexive

```agda
abstract
  refl-sim-ℂ : {l : Level} (z : ℂ l) → sim-ℂ z z
  refl-sim-ℂ (a , b) = (refl-sim-ℝ a , refl-sim-ℝ b)
```

### Similarity is symmetric

```agda
abstract
  symmetric-sim-ℂ :
    {l1 l2 : Level} {x : ℂ l1} {y : ℂ l2} → sim-ℂ x y → sim-ℂ y x
  symmetric-sim-ℂ (a~c , b~d) = (symmetric-sim-ℝ a~c , symmetric-sim-ℝ b~d)
```

### Similarity is transitive

```agda
abstract
  transitive-sim-ℂ :
    {l1 l2 l3 : Level} (x : ℂ l1) (y : ℂ l2) (z : ℂ l3) →
    sim-ℂ y z → sim-ℂ x y → sim-ℂ x z
  transitive-sim-ℂ (a , b) (c , d) (e , f) (c~e , d~f) (a~c , b~d) =
    ( transitive-sim-ℝ a c e c~e a~c , transitive-sim-ℝ b d f d~f b~d)
```

### Similarity characterizes equality at a universe level

```agda
abstract
  eq-sim-ℂ : {l : Level} {x y : ℂ l} → sim-ℂ x y → x ＝ y
  eq-sim-ℂ (a~c , b~d) = eq-ℂ (eq-sim-ℝ a~c) (eq-sim-ℝ b~d)
```
