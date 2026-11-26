# Apart subtypes

```agda
module measure-theory.apart-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Two [subtypes](foundation.subtypes.md) `A` and `B` of a type `X` equipped with
an [apartness relation](foundation.apartness-relations.md) are
{{#concept "apart" Disambiguation="subtypes of a type equipped with an apartness relation" Agda=apart-subtype-Type-With-Apartness}}
if every one of their elements is apart.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Type-With-Apartness l1 l2)
  (A : subtype l3 (type-Type-With-Apartness X))
  (B : subtype l4 (type-Type-With-Apartness X))
  where

  apart-prop-subtype-Type-With-Apartness : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  apart-prop-subtype-Type-With-Apartness =
    Π-Prop
      ( type-Type-With-Apartness X)
      ( λ a →
        Π-Prop
          ( type-Type-With-Apartness X)
          ( λ b →
            A a ⇒ B b ⇒ rel-apart-Type-With-Apartness X a b))

  apart-subtype-Type-With-Apartness : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  apart-subtype-Type-With-Apartness =
    type-Prop apart-prop-subtype-Type-With-Apartness
```
