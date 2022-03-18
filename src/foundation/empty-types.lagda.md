# Empty types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.empty-types where

open import foundation-core.empty-types public

open import foundation-core.dependent-pair-types using (pair; pr1; pr2)
open import foundation-core.embeddings using (is-emb; _↪_)
open import foundation-core.equivalences using
  ( is-equiv; is-equiv-has-inverse; _≃_; inv-equiv; _∘e_; map-inv-equiv)
open import foundation-core.functions using (_∘_; id)
open import foundation-core.homotopies using (_~_)
open import foundation-core.sets using (is-set; UU-Set)
open import foundation-core.truncated-types using
  ( is-trunc; Truncated-Type)
open import foundation-core.truncation-levels using (𝕋; succ-𝕋)
open import foundation-core.universe-levels using (Level; lzero; UU)

open import foundation.propositional-truncations using
  ( type-trunc-Prop; map-universal-property-trunc-Prop; unit-trunc-Prop)
open import foundation.propositions using
  ( is-prop; UU-Prop; is-trunc-is-prop; is-prop-function-type; is-prop-equiv')
open import foundation.raising-universe-levels using (raise; equiv-raise)
```

## Idea

An empty type is a type with no elements. The (standard) empty type is introduced as an inductive type with no constructors. With the standard empty type available, we will say that a type is empty if it maps into the standard empty type.

## Definition

### We raise the empty type to an arbitrary universe level

```agda
raise-empty : (l : Level) → UU l
raise-empty l = raise l empty

equiv-raise-empty : (l : Level) → empty ≃ raise-empty l
equiv-raise-empty l = equiv-raise l empty
```

## Properties


### Being empty is a proposition

```agda
is-prop-is-empty : {l : Level} {A : UU l} → is-prop (is-empty A)
is-prop-is-empty = is-prop-function-type is-prop-empty

is-empty-Prop : {l1 : Level} → UU l1 → UU-Prop l1
pr1 (is-empty-Prop A) = is-empty A
pr2 (is-empty-Prop A) = is-prop-is-empty

is-nonempty-Prop : {l1 : Level} → UU l1 → UU-Prop l1
pr1 (is-nonempty-Prop A) = is-nonempty A
pr2 (is-nonempty-Prop A) = is-prop-is-empty
```

```agda
abstract
  is-empty-type-trunc-Prop :
    {l1 : Level} {X : UU l1} → is-empty X → is-empty (type-trunc-Prop X)
  is-empty-type-trunc-Prop f =
    map-universal-property-trunc-Prop empty-Prop f

abstract
  is-empty-type-trunc-Prop' :
    {l1 : Level} {X : UU l1} → is-empty (type-trunc-Prop X) → is-empty X
  is-empty-type-trunc-Prop' f = f ∘ unit-trunc-Prop
```

### Any inhabited type is nonempty

```agda
abstract
  is-nonempty-is-inhabited :
    {l : Level} {X : UU l} → type-trunc-Prop X → is-nonempty X
  is-nonempty-is-inhabited {l} {X} =
    map-universal-property-trunc-Prop (is-nonempty-Prop X) (λ x f → f x)
```

```agda
abstract
  is-prop-raise-empty :
    {l1 : Level} → is-prop (raise-empty l1)
  is-prop-raise-empty {l1} =
    is-prop-equiv'
      ( equiv-raise l1 empty)
      ( is-prop-empty)

raise-empty-Prop :
  (l1 : Level) → UU-Prop l1
pr1 (raise-empty-Prop l1) = raise-empty l1
pr2 (raise-empty-Prop l1) = is-prop-raise-empty

abstract
  is-empty-raise-empty :
    {l1 : Level} → is-empty (raise-empty l1)
  is-empty-raise-empty {l1} = map-inv-equiv (equiv-raise-empty l1)
```
