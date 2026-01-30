# Full complemented subtypes

```agda
module measure-theory.full-complemented-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.empty-subtypes
open import foundation.empty-types
open import foundation.full-subtypes
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.unit-type
open import foundation.universe-levels

open import measure-theory.complemented-subtypes
open import measure-theory.large-poset-complemented-subtypes

open import order-theory.top-elements-large-posets
```

</details>

## Idea

A
{{#concept "full" Disambiguation="complemented subtype of a type with an apartness relation"}}
[complemented subtype](measure-theory.complemented-subtypes.md) of a type `X`
equipped with an [apartness relation](foundation.apartness-relations.md) is the
[full](foundation.full-subtypes.md) subtype paired with the
[empty](foundation.empty-subtypes.md) subtype.

## Definition

### The property of being a full complemented subtype

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Apartness l1 l2)
  where

  is-full-prop-complemented-subtype-Type-With-Apartness :
    {l : Level} → complemented-subtype-Type-With-Apartness X l → Prop (l1 ⊔ l)
  is-full-prop-complemented-subtype-Type-With-Apartness (A , A' , _) =
    is-full-prop-subtype A ∧ is-empty-prop-subtype A'

  is-full-complemented-subtype-Type-With-Apartness :
    {l : Level} → complemented-subtype-Type-With-Apartness X l → UU (l1 ⊔ l)
  is-full-complemented-subtype-Type-With-Apartness A =
    type-Prop (is-full-prop-complemented-subtype-Type-With-Apartness A)
```

### The canonical full complemented subtype

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Apartness l1 l2)
  where

  full-complemented-subtype-Type-With-Apartness :
    (l : Level) → complemented-subtype-Type-With-Apartness X l
  full-complemented-subtype-Type-With-Apartness l =
    ( full-subtype l (type-Type-With-Apartness X) ,
      empty-subtype l (type-Type-With-Apartness X) ,
      λ _ _ _ a'∈∅ → ex-falso (map-inv-raise a'∈∅))
```

## Properties

### The canonical full complemented subtype is full

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Apartness l1 l2)
  where

  abstract
    is-full-full-complemented-subtype-Type-With-Apartness :
      (l : Level) →
      is-full-complemented-subtype-Type-With-Apartness
        ( X)
        ( full-complemented-subtype-Type-With-Apartness X l)
    is-full-full-complemented-subtype-Type-With-Apartness l =
      ( ( λ _ → map-raise star) ,
        ( λ _ → map-inv-raise))
```

### The canonical full complemented subtype is the top element of the large poset of complemented subtypes

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Apartness l1 l2)
  where

  abstract
    is-top-element-full-complemented-subtype-Type-With-Apartness :
      (l : Level) →
      is-top-element-Large-Poset
        ( large-poset-complemented-subtype-Type-With-Apartness X)
        ( full-complemented-subtype-Type-With-Apartness X l)
    is-top-element-full-complemented-subtype-Type-With-Apartness
      l (A , A' , _) =
      ( ( λ _ _ → map-raise star) ,
        ( λ a' a'∈∅ → ex-falso (map-inv-raise a'∈∅)))
```
