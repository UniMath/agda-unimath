# Simplicial arrows

```agda
module simplicial-type-theory.simplicial-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negation
open import foundation.universe-levels

open import simplicial-type-theory.directed-interval-type
```

</details>

## Idea

A
{{#concept "simplicial arrow" Disambiguation="simplicial type theory" Agda=arrow▵}}
in a type `A` is a map from the
[directed interval](simplicial-type-theory.directed-interval-type.md) to the
type, `𝟚 → A`. Given a simplicial arrow `α` in `A`, we call `α 0₂` the _source_,
and `α 1₂` the _target_ of the arrow. See
[directed edges](simplicial-type-theory.directed-edges.md) for simplicial arrows
with a specified source and target.

## Definitions

### Simplicial arrows in types dependent over the directed interval

```agda
arrow▵' : {l : Level} → (𝟚 → UU l) → UU l
arrow▵' A = (t : 𝟚) → A t
```

### Simplicial arrows

```agda
arrow▵ : {l : Level} → UU l → UU l
arrow▵ A = arrow▵' (λ _ → A)
```

### The identity/constant simplicial arrows

```agda
id-arrow▵ : {l : Level} {A : UU l} → A → arrow▵ A
id-arrow▵ x _ = x
```

### The representing arrow of the directed interval

```agda
representing-arrow-𝟚 : arrow▵ 𝟚
representing-arrow-𝟚 = id
```

### Simplicial arrows arising from equalities

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  arrow▵-eq : x ＝ y → arrow▵ A
  arrow▵-eq refl = id-arrow▵ x

  compute-source-arrow▵-eq :
    (p : x ＝ y) → arrow▵-eq p 0₂ ＝ x
  compute-source-arrow▵-eq refl = refl

  compute-target-arrow▵-eq :
    (p : x ＝ y) → arrow▵-eq p 1₂ ＝ y
  compute-target-arrow▵-eq refl = refl
```

## Properties

### The representing arrow of the directed interval is not constant

```agda
is-not-constant-representing-arrow-𝟚 :
  (t : 𝟚) → ¬ (representing-arrow-𝟚 ~ id-arrow▵ t)
is-not-constant-representing-arrow-𝟚 _ H = is-nontrivial-𝟚 (H 0₂ ∙ inv (H 1₂))
```
