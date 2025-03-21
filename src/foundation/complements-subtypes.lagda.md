# Complements of subtypes

```agda
module foundation.complements-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.sections
open import foundation.equality-dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.retractions
open import foundation.propositions
open import foundation.equivalences
open import foundation.dependent-pair-types
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.double-negation-stable-propositions
open import foundation.full-subtypes
open import foundation.negation
open import foundation.postcomposition-functions
open import foundation.powersets
open import foundation.propositional-truncations
open import foundation.unions-subtypes
open import foundation.universe-levels
open import foundation.functoriality-coproduct-types
open import foundation.type-arithmetic-coproduct-types

open import foundation.action-on-identifications-functions
open import foundation-core.function-types
open import foundation-core.subtypes

open import logic.double-negation-stable-subtypes

open import order-theory.large-posets
open import order-theory.opposite-large-posets
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.order-preserving-maps-posets
open import order-theory.order-preserving-maps-preorders
open import order-theory.posets
```

</details>

## Idea

The
{{#concept "complement" Disambiguation="of a subtype" Agda=complement-subtype}}
of a [subtype](foundation-core.subtypes.md) `P ⊆ A` consists of the elements
that are [not](foundation-core.negation.md) in `P`.

## Definition

### Complements of subtypes

```agda
complement-subtype :
  {l1 l2 : Level} {A : UU l1} → subtype l2 A → subtype l2 A
complement-subtype P x = neg-Prop (P x)
```

## Properties

### Complements of subtypes are double negation stable

```agda
complement-double-negation-stable-subtype' :
  {l1 l2 : Level} {A : UU l1} →
  subtype l2 A → double-negation-stable-subtype l2 A
complement-double-negation-stable-subtype' P x =
  neg-type-Double-Negation-Stable-Prop (is-in-subtype P x)
```

### Taking complements gives a contravariant endooperator on the powerset posets

```agda
neg-hom-powerset :
  {l1 : Level} {A : UU l1} →
  hom-Large-Poset
    ( λ l → l)
    ( powerset-Large-Poset A)
    ( opposite-Large-Poset (powerset-Large-Poset A))
neg-hom-powerset =
  make-hom-Large-Preorder
    ( λ P x → neg-Prop (P x))
    ( λ P Q f x → map-neg (f x))
```

### Complementation reverses the containment order on subsets

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1}
  (B : subtype l2 A)
  (C : subtype l3 A)
  where

  reverses-order-complement-subtype :
    B ⊆ C →
    complement-subtype C ⊆ complement-subtype B
  reverses-order-complement-subtype B⊆C x x∉C x∈B = x∉C (B⊆C x x∈B)
```

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
      ( inr )
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
