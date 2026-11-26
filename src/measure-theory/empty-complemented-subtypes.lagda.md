# Empty complemented subtypes

```agda
module measure-theory.empty-complemented-subtypes where
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

open import order-theory.bottom-elements-large-posets
```

</details>

## Idea

An
{{#concept "empty" Disambiguation="complemented subtype of a type with an apartness relation"}}
[complemented subtype](measure-theory.complemented-subtypes.md) of a type `X`
equipped with an [apartness relation](foundation.apartness-relations.md) is the
[empty](foundation.empty-subtypes.md) subtype paired with the
[full](foundation.full-subtypes.md) subtype.

## Definition

### The property of being an empty complemented subtype

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Apartness l1 l2)
  where

  is-empty-prop-complemented-subtype-Type-With-Apartness :
    {l : Level} → complemented-subtype-Type-With-Apartness X l → Prop (l1 ⊔ l)
  is-empty-prop-complemented-subtype-Type-With-Apartness (A , A' , _) =
    is-empty-prop-subtype A ∧ is-full-prop-subtype A'

  is-empty-complemented-subtype-Type-With-Apartness :
    {l : Level} → complemented-subtype-Type-With-Apartness X l → UU (l1 ⊔ l)
  is-empty-complemented-subtype-Type-With-Apartness A =
    type-Prop (is-empty-prop-complemented-subtype-Type-With-Apartness A)
```

### The canonical empty complemented subtype

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Apartness l1 l2)
  where

  empty-complemented-subtype-Type-With-Apartness :
    (l : Level) → complemented-subtype-Type-With-Apartness X l
  empty-complemented-subtype-Type-With-Apartness l =
    ( empty-subtype l (type-Type-With-Apartness X) ,
      full-subtype l (type-Type-With-Apartness X) ,
      λ _ _ a∈∅ _ → ex-falso (map-inv-raise a∈∅))
```

## Properties

### The canonical empty complemented subtype is empty

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Apartness l1 l2)
  where

  abstract
    is-empty-empty-complemented-subtype-Type-With-Apartness :
      (l : Level) →
      is-empty-complemented-subtype-Type-With-Apartness
        ( X)
        ( empty-complemented-subtype-Type-With-Apartness X l)
    is-empty-empty-complemented-subtype-Type-With-Apartness l =
      ( ( λ _ → map-inv-raise) ,
        ( λ _ → map-raise star))
```

### The canonical empty complemented subtype is the bottom element of the large poset of complemented subtypes

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Apartness l1 l2)
  where

  abstract
    is-bottom-element-empty-complemented-subtype-Type-With-Apartness :
      (l : Level) →
      is-bottom-element-Large-Poset
        ( large-poset-complemented-subtype-Type-With-Apartness X)
        ( empty-complemented-subtype-Type-With-Apartness X l)
    is-bottom-element-empty-complemented-subtype-Type-With-Apartness
      l (A , A' , _) =
      ( ( λ _ a∈∅ → ex-falso (map-inv-raise a∈∅)) ,
        ( λ _ _ → map-raise star))
```
