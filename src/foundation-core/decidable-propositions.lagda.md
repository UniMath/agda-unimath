# Decidable propositions

```agda
module foundation-core.decidable-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Idea

A {{#concept "decidable proposition" Agda=is-decidable-Prop}} is a
[proposition](foundation-core.propositions.md) that has a
[decidable](foundation.decidable-types.md) underlying type.

## Definitions

### The property of a proposition of being decidable

```agda
is-prop-is-decidable :
  {l : Level} {A : UU l} → is-prop A → is-prop (is-decidable A)
is-prop-is-decidable is-prop-A =
  is-prop-coproduct intro-double-negation is-prop-A is-prop-neg

is-decidable-Prop :
  {l : Level} → Prop l → Prop l
pr1 (is-decidable-Prop P) = is-decidable (type-Prop P)
pr2 (is-decidable-Prop P) = is-prop-is-decidable (is-prop-type-Prop P)

is-decidable-type-Prop : {l : Level} → Prop l → UU l
is-decidable-type-Prop P = is-decidable (type-Prop P)
```

### The subuniverse of decidable propositions

```agda
is-decidable-prop : {l : Level} → UU l → UU l
is-decidable-prop A = is-prop A × is-decidable A

is-prop-is-decidable-prop :
  {l : Level} (X : UU l) → is-prop (is-decidable-prop X)
is-prop-is-decidable-prop X =
  is-prop-has-element
    ( λ H →
      is-prop-product
        ( is-prop-is-prop X)
        ( is-prop-is-decidable (pr1 H)))

is-decidable-prop-Prop :
  {l : Level} (A : UU l) → Prop l
pr1 (is-decidable-prop-Prop A) = is-decidable-prop A
pr2 (is-decidable-prop-Prop A) = is-prop-is-decidable-prop A

module _
  {l : Level} {A : UU l} (H : is-decidable-prop A)
  where

  is-prop-type-is-decidable-prop : is-prop A
  is-prop-type-is-decidable-prop = pr1 H

  is-decidable-type-is-decidable-prop : is-decidable A
  is-decidable-type-is-decidable-prop = pr2 H
```

### Decidable propositions

```agda
Decidable-Prop :
  (l : Level) → UU (lsuc l)
Decidable-Prop l = type-subtype is-decidable-prop-Prop

module _
  {l : Level} (P : Decidable-Prop l)
  where

  prop-Decidable-Prop : Prop l
  prop-Decidable-Prop = tot (λ x → pr1) P

  type-Decidable-Prop : UU l
  type-Decidable-Prop = type-Prop prop-Decidable-Prop

  abstract
    is-prop-type-Decidable-Prop : is-prop type-Decidable-Prop
    is-prop-type-Decidable-Prop = is-prop-type-Prop prop-Decidable-Prop

  is-decidable-Decidable-Prop : is-decidable type-Decidable-Prop
  is-decidable-Decidable-Prop = pr2 (pr2 P)

  is-decidable-prop-type-Decidable-Prop : is-decidable-prop type-Decidable-Prop
  is-decidable-prop-type-Decidable-Prop = pr2 P

  is-decidable-prop-Decidable-Prop : Prop l
  pr1 is-decidable-prop-Decidable-Prop =
    is-decidable type-Decidable-Prop
  pr2 is-decidable-prop-Decidable-Prop =
    is-prop-is-decidable is-prop-type-Decidable-Prop
```

### The empty type is a decidable proposition

```agda
is-decidable-prop-empty : is-decidable-prop empty
pr1 is-decidable-prop-empty = is-prop-empty
pr2 is-decidable-prop-empty = inr id

empty-Decidable-Prop : Decidable-Prop lzero
pr1 empty-Decidable-Prop = empty
pr2 empty-Decidable-Prop = is-decidable-prop-empty
```

### Empty types are decidable propositions

```agda
is-decidable-prop-is-empty :
  {l : Level} {A : UU l} → is-empty A → is-decidable-prop A
is-decidable-prop-is-empty H = is-prop-is-empty H , inr H
```

### The unit type is a decidable proposition

```agda
is-decidable-prop-unit : is-decidable-prop unit
pr1 is-decidable-prop-unit = is-prop-unit
pr2 is-decidable-prop-unit = inl star

unit-Decidable-Prop : Decidable-Prop lzero
pr1 unit-Decidable-Prop = unit
pr2 unit-Decidable-Prop = is-decidable-prop-unit
```

### Contractible types are decidable propositions

```agda
is-decidable-prop-is-contr :
  {l : Level} {A : UU l} → is-contr A → is-decidable-prop A
is-decidable-prop-is-contr H = is-prop-is-contr H , inl (center H)
```

### The product of two decidable propositions is a decidable proposition

```agda
module _
  {l1 l2 : Level} (P : Decidable-Prop l1) (Q : Decidable-Prop l2)
  where

  type-product-Decidable-Prop : UU (l1 ⊔ l2)
  type-product-Decidable-Prop =
    type-product-Prop (prop-Decidable-Prop P) (prop-Decidable-Prop Q)

  is-prop-product-Decidable-Prop : is-prop type-product-Decidable-Prop
  is-prop-product-Decidable-Prop =
    is-prop-product-Prop (prop-Decidable-Prop P) (prop-Decidable-Prop Q)

  is-decidable-product-Decidable-Prop : is-decidable type-product-Decidable-Prop
  is-decidable-product-Decidable-Prop =
    is-decidable-product
      ( is-decidable-Decidable-Prop P)
      ( is-decidable-Decidable-Prop Q)

  is-decidable-prop-product-Decidable-Prop :
    is-decidable-prop type-product-Decidable-Prop
  pr1 is-decidable-prop-product-Decidable-Prop = is-prop-product-Decidable-Prop
  pr2 is-decidable-prop-product-Decidable-Prop =
    is-decidable-product-Decidable-Prop

  product-Decidable-Prop : Decidable-Prop (l1 ⊔ l2)
  pr1 product-Decidable-Prop = type-product-Decidable-Prop
  pr2 product-Decidable-Prop = is-decidable-prop-product-Decidable-Prop
```

### The dependent sum of a family of decidable propositions over a decidable proposition

```agda
module _
  {l1 l2 : Level} {P : UU l1} {Q : P → UU l2}
  (H : is-decidable-prop P) (K : (x : P) → is-decidable-prop (Q x))
  where

  is-prop-is-decidable-prop-Σ : is-prop (Σ P Q)
  is-prop-is-decidable-prop-Σ =
    is-prop-Σ
      ( is-prop-type-is-decidable-prop H)
      ( is-prop-type-is-decidable-prop ∘ K)

  is-decidable-is-decidable-prop-Σ : is-decidable (Σ P Q)
  is-decidable-is-decidable-prop-Σ =
    rec-coproduct
      ( λ x →
        rec-coproduct
          ( λ y → inl (x , y))
          ( λ ny →
            inr
              ( λ xy →
                ny
                  ( tr Q
                    ( eq-is-prop (is-prop-type-is-decidable-prop H))
                    ( pr2 xy))))
          ( is-decidable-type-is-decidable-prop (K x)))
      ( λ nx → inr (λ xy → nx (pr1 xy)))
      ( is-decidable-type-is-decidable-prop H)

  is-decidable-prop-Σ : is-decidable-prop (Σ P Q)
  is-decidable-prop-Σ =
    ( is-prop-is-decidable-prop-Σ , is-decidable-is-decidable-prop-Σ)
```

### The negation operation on decidable propositions

```agda
is-decidable-prop-neg :
  {l1 : Level} {A : UU l1} → is-decidable A → is-decidable-prop (¬ A)
is-decidable-prop-neg is-decidable-A =
  ( is-prop-neg , is-decidable-neg is-decidable-A)

neg-type-Decidable-Prop :
  {l1 : Level} (A : UU l1) → is-decidable A → Decidable-Prop l1
neg-type-Decidable-Prop A is-decidable-A =
  ( ¬ A , is-decidable-prop-neg is-decidable-A)

neg-Decidable-Prop :
  {l1 : Level} → Decidable-Prop l1 → Decidable-Prop l1
neg-Decidable-Prop P =
  neg-type-Decidable-Prop
    ( type-Decidable-Prop P)
    ( is-decidable-Decidable-Prop P)

type-neg-Decidable-Prop :
  {l1 : Level} → Decidable-Prop l1 → UU l1
type-neg-Decidable-Prop P = type-Decidable-Prop (neg-Decidable-Prop P)
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
