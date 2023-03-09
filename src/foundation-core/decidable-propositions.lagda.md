# Decidable propositions

```agda
module foundation-core.decidable-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.double-negation
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.unit-type

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.empty-types
open import foundation-core.functions
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.universe-levels
```

</details>

## Idea

A decidable proposition is a proposition that has a decidable underlying type.

## Definition

### The subtype of decidable propositions

```agda
is-decidable-prop : {l : Level} → UU l → UU l
is-decidable-prop A = is-prop A × is-decidable A

is-prop-is-decidable :
  {l : Level} {A : UU l} → is-prop A → is-prop (is-decidable A)
is-prop-is-decidable is-prop-A =
  is-prop-coprod intro-dn is-prop-A is-prop-neg

is-decidable-Prop :
  {l : Level} → Prop l → Prop l
pr1 (is-decidable-Prop P) = is-decidable (type-Prop P)
pr2 (is-decidable-Prop P) = is-prop-is-decidable (is-prop-type-Prop P)

is-prop-is-decidable-prop :
  {l : Level} (X : UU l) → is-prop (is-decidable-prop X)
is-prop-is-decidable-prop X =
  is-prop-is-inhabited
    ( λ H →
      is-prop-prod
        ( is-prop-is-prop X)
        ( is-prop-is-decidable (pr1 H)))

is-decidable-prop-Prop :
  {l : Level} (A : UU l) → Prop l
pr1 (is-decidable-prop-Prop A) = is-decidable-prop A
pr2 (is-decidable-prop-Prop A) = is-prop-is-decidable-prop A
```

### Decidable propositions

```agda
decidable-Prop :
  (l : Level) → UU (lsuc l)
decidable-Prop l = type-subtype is-decidable-prop-Prop

module _
  {l : Level} (P : decidable-Prop l)
  where

  prop-decidable-Prop : Prop l
  prop-decidable-Prop = tot (λ x → pr1) P

  type-decidable-Prop : UU l
  type-decidable-Prop = type-Prop prop-decidable-Prop

  abstract
    is-prop-type-decidable-Prop : is-prop type-decidable-Prop
    is-prop-type-decidable-Prop = is-prop-type-Prop prop-decidable-Prop

  is-decidable-type-decidable-Prop : is-decidable type-decidable-Prop
  is-decidable-type-decidable-Prop = pr2 (pr2 P)

  is-decidable-prop-type-decidable-Prop : is-decidable-prop type-decidable-Prop
  is-decidable-prop-type-decidable-Prop = pr2 P

  is-decidable-prop-decidable-Prop : Prop l
  pr1 is-decidable-prop-decidable-Prop = is-decidable type-decidable-Prop
  pr2 is-decidable-prop-decidable-Prop =
    is-prop-is-decidable is-prop-type-decidable-Prop
```

### The empty type is a decidable proposition

```agda
is-decidable-prop-empty : is-decidable-prop empty
pr1 is-decidable-prop-empty = is-prop-empty
pr2 is-decidable-prop-empty = inr id

empty-decidable-Prop : decidable-Prop lzero
pr1 empty-decidable-Prop = empty
pr2 empty-decidable-Prop = is-decidable-prop-empty
```

### The unit type is a decidable proposition

```agda
is-decidable-prop-unit : is-decidable-prop unit
pr1 is-decidable-prop-unit = is-prop-unit
pr2 is-decidable-prop-unit = inl star

unit-decidable-Prop : decidable-Prop lzero
pr1 unit-decidable-Prop = unit
pr2 unit-decidable-Prop = is-decidable-prop-unit
```

### Decidability of a propositional truncation

```agda
abstract
  is-prop-is-decidable-trunc-Prop :
    {l : Level} (A : UU l) → is-prop (is-decidable (type-trunc-Prop A))
  is-prop-is-decidable-trunc-Prop A =
    is-prop-is-decidable is-prop-type-trunc-Prop

is-decidable-trunc-Prop : {l : Level} → UU l → Prop l
pr1 (is-decidable-trunc-Prop A) = is-decidable (type-trunc-Prop A)
pr2 (is-decidable-trunc-Prop A) = is-prop-is-decidable-trunc-Prop A

is-decidable-trunc-Prop-is-merely-decidable :
  {l : Level} (A : UU l) →
  is-merely-decidable A → is-decidable (type-trunc-Prop A)
is-decidable-trunc-Prop-is-merely-decidable A =
  map-universal-property-trunc-Prop
    ( is-decidable-trunc-Prop A)
    ( f)
  where
  f : is-decidable A → type-Prop (is-decidable-trunc-Prop A)
  f (inl a) = inl (unit-trunc-Prop a)
  f (inr f) = inr (map-universal-property-trunc-Prop empty-Prop f)

is-merely-decidable-is-decidable-trunc-Prop :
  {l : Level} (A : UU l) →
  is-decidable (type-trunc-Prop A) → is-merely-decidable A
is-merely-decidable-is-decidable-trunc-Prop A (inl x) =
   apply-universal-property-trunc-Prop x
     ( is-merely-decidable-Prop A)
     ( unit-trunc-Prop ∘ inl)
is-merely-decidable-is-decidable-trunc-Prop A (inr f) =
  unit-trunc-Prop (inr (f ∘ unit-trunc-Prop))
```
