# Subuniverse parametric types

```agda
module foundation.subuniverse-parametric-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions
open import foundation.dependent-products-truncated-types
open import foundation.double-negation-stable-propositions
open import foundation.empty-types
open import foundation.full-subuniverses
open import foundation.parametric-types
open import foundation.propositional-extensionality
open import foundation.retracts-of-types
open import foundation.set-truncations
open import foundation.sets
open import foundation.subuniverses
open import foundation.truncations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.propositions
open import foundation-core.truncated-types
open import foundation-core.truncation-levels

open import orthogonal-factorization-systems.null-types
```

</details>

## Idea

Given a [subuniverse](foundation.subuniverses.md) `K`, a type `X : 𝒰` is
`K`-{{#concept "parametric" Disambiguation="type" Agda=is-subuniverse-parametric Agda=Subuniverse-Parametric-Type}}
if the [constant map](foundation.constant-maps.md) `X → (K → X)` is an
[equivalence](foundation-core.equivalences.md). In other words, if `X` is
`K`-[null](orthogonal-factorization-systems.null-types.md).

## Definitions

### The predicate on a type of being parametric at a subuniverse

```agda
module _
  {l1 l2 l3 : Level} (P : subuniverse l2 l3) (X : UU l1)
  where

  is-subuniverse-parametric : UU (l1 ⊔ lsuc l2 ⊔ l3)
  is-subuniverse-parametric = is-null (type-subuniverse P) X

  is-prop-is-subuniverse-parametric : is-prop is-subuniverse-parametric
  is-prop-is-subuniverse-parametric = is-prop-is-null (type-subuniverse P) X

  is-subuniverse-parametric-Prop : Prop (l1 ⊔ lsuc l2 ⊔ l3)
  is-subuniverse-parametric-Prop = is-null-Prop (type-subuniverse P) X
```

### The predicate on a type of being parametric at the full subuniverse

```agda
module _
  {l1 : Level} (l2 : Level) (X : UU l1)
  where

  is-parametric-full-subuniverse : UU (l1 ⊔ lsuc l2)
  is-parametric-full-subuniverse =
    is-subuniverse-parametric (full-subuniverse l2 lzero) X

  is-prop-is-parametric-full-subuniverse :
    is-prop is-parametric-full-subuniverse
  is-prop-is-parametric-full-subuniverse =
    is-prop-is-subuniverse-parametric (full-subuniverse l2 lzero) X

  is-parametric-full-subuniverse-Prop : Prop (l1 ⊔ lsuc l2)
  is-parametric-full-subuniverse-Prop =
    is-subuniverse-parametric-Prop (full-subuniverse l2 lzero) X
```

## Properties

### Parametricity is equivalent to full-subuniverse parametricity

```agda
equiv-type-full-subuniverse :
  {l : Level} → type-subuniverse (full-subuniverse l lzero) ≃ UU l
equiv-type-full-subuniverse {l} =
  equiv-inclusion-full-subuniverse {l1 = l} {l2 = lzero}

module _
  {l1 l2 : Level} {X : UU l1}
  where

  is-parametric-is-parametric-full-subuniverse :
    is-parametric l2 X → is-parametric-full-subuniverse l2 X
  is-parametric-is-parametric-full-subuniverse =
    is-null-equiv-exponent equiv-type-full-subuniverse

  is-parametric-full-subuniverse-is-parametric :
    is-parametric-full-subuniverse l2 X → is-parametric l2 X
  is-parametric-full-subuniverse-is-parametric =
    is-null-equiv-exponent (inv-equiv equiv-type-full-subuniverse)
```

### Parametric types are parametric at subuniverses that are retracts of the universe

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l2 l3) {X : UU l1}
  where abstract

  is-parametric-retract-universe :
    type-subuniverse K retract-of UU l4 →
    is-parametric l4 X →
    is-subuniverse-parametric K X
  is-parametric-retract-universe = is-null-retract-exponent
```

### Subuniverse-parametric types are parametric at retracts of the subuniverse

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (K : subuniverse l2 l3) (L : subuniverse l4 l5) {X : UU l1}
  where abstract

  is-parametric-retract-subuniverse :
    type-subuniverse K retract-of type-subuniverse L →
    is-subuniverse-parametric L X →
    is-subuniverse-parametric K X
  is-parametric-retract-subuniverse = is-null-retract-exponent
```

### Parametric types are parametric at propositions

```agda
abstract
  is-prop-parametric-is-parametric :
    {l1 l2 : Level} {X : UU l1} →
    is-parametric l2 X → is-null (Prop l2) X
  is-prop-parametric-is-parametric =
    is-parametric-retract-universe is-prop-Prop retract-Prop-UU
```

### Parametric types are parametric at truncated types

```agda
abstract
  is-trunc-parametric-is-parametric :
    {l1 l2 : Level} (k : 𝕋) {X : UU l1} →
    is-parametric l2 X → is-null (Truncated-Type l2 k) X
  is-trunc-parametric-is-parametric k =
    is-parametric-retract-universe
      ( is-trunc-Prop k)
      ( retract-Truncated-Type-UU k)
```

### Parametric types are parametric at sets

```agda
abstract
  is-set-parametric-is-parametric :
    {l1 l2 : Level} {X : UU l1} →
    is-parametric l2 X → is-null (Set l2) X
  is-set-parametric-is-parametric =
    is-parametric-retract-universe is-set-Prop retract-Set-UU
```

### Parametric types are parametric at double negation stable propositions

```agda
abstract
  is-¬¬-parametric-is-parametric :
    {l1 l2 : Level} {X : UU l1} →
    is-parametric l2 X →
    is-subuniverse-parametric (is-double-negation-stable-prop-Prop {l2}) X
  is-¬¬-parametric-is-parametric =
    is-parametric-retract-universe
      ( is-double-negation-stable-prop-Prop)
      ( retract-Double-Negation-Stable-Prop-UU)
```

### Parametricity at propositions implies parametricity at double negation stable propositions

```agda
abstract
  is-¬¬-parametric-is-prop-parametric :
    {l1 l2 : Level} {X : UU l1} →
    is-subuniverse-parametric (is-prop-Prop {l2}) X →
    is-subuniverse-parametric (is-double-negation-stable-prop-Prop {l2}) X
  is-¬¬-parametric-is-prop-parametric {X} =
    is-parametric-retract-subuniverse
      ( is-double-negation-stable-prop-Prop)
      ( is-prop-Prop)
      ( retract-Double-Negation-Stable-Prop-Prop)
```

### Contractible types are parametric at any subuniverse

```agda
abstract
  is-subuniverse-parametric-is-contr :
    {l1 l2 l3 : Level} (K : subuniverse l2 l3) {X : UU l1} →
    is-contr X →
    is-subuniverse-parametric K X
  is-subuniverse-parametric-is-contr K =
    is-null-is-contr (type-subuniverse K)
```

### The unit type is parametric at any subuniverse

```agda
abstract
  is-subuniverse-parametric-unit :
    {l1 l2 : Level} (K : subuniverse l1 l2) →
    is-subuniverse-parametric K unit
  is-subuniverse-parametric-unit K =
    is-subuniverse-parametric-is-contr K is-contr-unit
```

### The empty type is parametric at a pointed subuniverse

```agda
abstract
  is-subuniverse-parametric-empty :
    {l1 l2 : Level} (K : subuniverse l1 l2) →
    type-subuniverse K →
    is-subuniverse-parametric K empty
  is-subuniverse-parametric-empty K y =
    is-null-is-prop-is-inhabited' {Y = type-subuniverse K} y is-prop-empty
```
