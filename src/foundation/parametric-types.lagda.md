# Parametric types

```agda
module foundation.parametric-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.evaluation-functions
open import foundation.retracts-of-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions

open import orthogonal-factorization-systems.null-types
```

</details>

## Idea

A type `X : 𝒰` is
{{#concept "parametric" Disambiguation="type" Agda=is-parametric Agda=Parametric-Type}}
if the [constant map](foundation.constant-maps.md) `X → (𝒰 → X)` is an
[equivalence](foundation-core.equivalences.md). In other words, if `X` is
`𝒰`-[null](orthogonal-factorization-systems.null-types.md).

## Definitions

### The predicate on a type of being parametric

```agda
module _
  {l1 : Level} (l2 : Level) (X : UU l1)
  where

  is-parametric : UU (l1 ⊔ lsuc l2)
  is-parametric = is-null (UU l2) X

  is-prop-is-parametric : is-prop is-parametric
  is-prop-is-parametric = is-prop-is-null (UU l2) X

  is-parametric-Prop : Prop (l1 ⊔ lsuc l2)
  is-parametric-Prop = is-null-Prop (UU l2) X
```

### The universe of parametric types

```agda
Parametric-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Parametric-Type l1 l2 = Σ (UU l1) (is-parametric l2)

module _
  {l1 l2 : Level} (X : Parametric-Type l1 l2)
  where

  type-Parametric-Type : UU l1
  type-Parametric-Type = pr1 X

  is-parametric-type-Parametric-Type :
    is-parametric l2 type-Parametric-Type
  is-parametric-type-Parametric-Type = pr2 X
```

## Properties

### Parametric types are closed under equivalences

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
  where abstract

  is-parametric-equiv :
    X ≃ Y → is-parametric l3 Y → is-parametric l3 X
  is-parametric-equiv = is-null-equiv-base

  is-parametric-equiv' :
    X ≃ Y → is-parametric l3 X → is-parametric l3 Y
  is-parametric-equiv' = is-null-equiv-base ∘ inv-equiv
```

### Parametric types are closed under retracts

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
  where abstract

  is-parametric-retract :
    X retract-of Y → is-parametric l3 Y → is-parametric l3 X
  is-parametric-retract = is-null-retract-base
```

### Contractible types are parametric

```agda
abstract
  is-parametric-is-contr :
    {l1 l2 : Level} {X : UU l1} →
    is-contr X → is-parametric l2 X
  is-parametric-is-contr {l2 = l2} =
    is-null-is-contr (UU l2)
```

### The unit type is parametric

```agda
abstract
  is-parametric-unit :
    {l : Level} → is-parametric l unit
  is-parametric-unit {l} =
    is-parametric-is-contr is-contr-unit
```

### The empty type is parametric

```agda
abstract
  is-parametric-empty :
    {l : Level} → is-parametric l empty
  is-parametric-empty {l} =
    is-equiv-is-empty _ (ev (raise-empty l))
```

### Propositions are parametric

```agda
abstract
  is-parametric-is-prop :
    {l1 l2 : Level} {X : UU l1} →
    is-prop X → is-parametric l2 X
  is-parametric-is-prop {l1} {l2} H =
    is-null-is-prop H (ev (raise-empty l2))
```
