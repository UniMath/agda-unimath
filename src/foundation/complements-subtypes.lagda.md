# Complements of subtypes

```agda
module foundation.complements-subtypes where
```

<details><summary>Imports</summary>

```agda
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
