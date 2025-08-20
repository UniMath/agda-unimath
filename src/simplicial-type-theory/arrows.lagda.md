# Arrows

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.arrows
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negation
open import foundation.universe-levels

open import simplicial-type-theory.directed-interval-type I
```

</details>

## Idea

An {{#concept "arrow" Disambiguation="in a simplicial type" Agda=arrow▵}} in a
type `A` is a map from the
[directed interval](simplicial-type-theory.directed-interval-type.md) to the
type, `Δ¹ → A`. Given a simplicial arrow `α` in `A`, we call `α 0▵` the
_source_, and `α 1▵` the _target_ of the arrow. See
[directed edges](simplicial-type-theory.directed-edges.md) for simplicial arrows
with a specified source and target.

## Definitions

### Arrows in types over the directed interval

```agda
arrow▵' : {l : Level} → (Δ¹ → UU l) → UU (I1 ⊔ l)
arrow▵' A = (t : Δ¹) → A t
```

### Arrows

```agda
arrow▵ : {l : Level} → UU l → UU (I1 ⊔ l)
arrow▵ A = arrow▵' (λ _ → A)
```

### The identity/constant arrows

```agda
id-arrow▵ : {l : Level} {A : UU l} → A → arrow▵ A
id-arrow▵ x _ = x
```

### The representing arrow of the directed interval

```agda
representing-arrow-Δ¹ : arrow▵ Δ¹
representing-arrow-Δ¹ = id
```

### Arrows arising from identifications

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  arrow▵-eq : x ＝ y → arrow▵ A
  arrow▵-eq refl = id-arrow▵ x

  compute-source-arrow▵-eq :
    (p : x ＝ y) → arrow▵-eq p 0▵ ＝ x
  compute-source-arrow▵-eq refl = refl

  compute-target-arrow▵-eq :
    (p : x ＝ y) → arrow▵-eq p 1▵ ＝ y
  compute-target-arrow▵-eq refl = refl
```

## Properties

### The representing arrow of the directed interval is not constant

```agda
is-not-constant-representing-arrow-Δ¹ :
  (t : Δ¹) → ¬ (representing-arrow-Δ¹ ~ id-arrow▵ t)
is-not-constant-representing-arrow-Δ¹ _ H = is-nontrivial-Δ¹ (H 0▵ ∙ inv (H 1▵))
```
