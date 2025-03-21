# Complements of decidable subtypes

```agda
module foundation.complements-decidable-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "complement" Disambiguation="of a decidable subtype" Agda=complement-decidable-subtype}}
of a [decidable subtype](foundation.decidable-subtypes.md) `P ⊆ A` consists of
the elements that are [not](foundation-core.negation.md) in `P`.

### The complement of a decidable subtype is decidable

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (P : decidable-subtype l2 A)
  where

  complement-decidable-subtype : decidable-subtype l2 A
  complement-decidable-subtype a = neg-Decidable-Prop (P a)
```

### For a decidable subtype `P`, a type is equivalent to the coproduct of `P` and its complement

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (P : decidable-subtype l2 A)
  where

  map-equiv-coproduct-decidable-subtype-complement :
    A →
    type-decidable-subtype P +
    type-decidable-subtype (complement-decidable-subtype P)
  map-equiv-coproduct-decidable-subtype-complement a with
    is-decidable-Decidable-Prop (P a)
  ... | inl pa = inl (a , pa)
  ... | inr ¬pa = inr (a , ¬pa)

  map-inv-equiv-coproduct-decidable-subtype-complement :
    type-decidable-subtype P +
    type-decidable-subtype (complement-decidable-subtype P) → A
  map-inv-equiv-coproduct-decidable-subtype-complement (inl (a , _)) = a
  map-inv-equiv-coproduct-decidable-subtype-complement (inr (a , _)) = a

  is-section-map-inv-equiv-coproduct-decidable-subtype-complement :
    is-section
      map-equiv-coproduct-decidable-subtype-complement
      map-inv-equiv-coproduct-decidable-subtype-complement
  is-section-map-inv-equiv-coproduct-decidable-subtype-complement (inl (a , pa))
    with is-decidable-Decidable-Prop (P a)
  ... | inl pa' =
    ap inl (eq-pair-eq-fiber (eq-type-Prop (prop-Decidable-Prop (P a))))
  ... | inr ¬pa' = ex-falso (¬pa' pa)
  is-section-map-inv-equiv-coproduct-decidable-subtype-complement
    (inr (a , ¬pa)) with is-decidable-Decidable-Prop (P a)
  ... | inl pa' = ex-falso (¬pa pa')
  ... | inr ¬pa' =
    ap
      ( inr)
      ( eq-pair-eq-fiber (eq-type-Prop (neg-Prop (prop-Decidable-Prop (P a)))))

  is-retraction-map-inv-equiv-coproduct-decidable-subtype-complement :
    is-retraction
      map-equiv-coproduct-decidable-subtype-complement
      map-inv-equiv-coproduct-decidable-subtype-complement
  is-retraction-map-inv-equiv-coproduct-decidable-subtype-complement a
    with is-decidable-Decidable-Prop (P a)
  ... | inl _ = refl
  ... | inr _ = refl

  equiv-coproduct-decidable-subtype-complement :
    A ≃
    type-decidable-subtype P +
    type-decidable-subtype (complement-decidable-subtype P)
  equiv-coproduct-decidable-subtype-complement =
    map-equiv-coproduct-decidable-subtype-complement ,
    ( map-inv-equiv-coproduct-decidable-subtype-complement ,
      is-section-map-inv-equiv-coproduct-decidable-subtype-complement) ,
    ( map-inv-equiv-coproduct-decidable-subtype-complement ,
      is-retraction-map-inv-equiv-coproduct-decidable-subtype-complement)
```
