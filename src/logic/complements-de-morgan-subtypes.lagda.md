# Complements of De Morgan subtypes

```agda
module logic.complements-de-morgan-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.complements-subtypes
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.full-subtypes
open import foundation.involutions
open import foundation.negation
open import foundation.postcomposition-functions
open import foundation.powersets
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.universe-levels

open import foundation-core.function-types

open import logic.complements-decidable-subtypes
open import logic.de-morgan-propositions
open import logic.de-morgan-subtypes

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
{{#concept "complement" Disambiguation="of a De Morgan subtype" Agda=complement-de-morgan-subtype}}
of a [De Morgan subtype](foundation.de-morgan-subtypes.md) `B ⊆ A` consists of
the elements that are not in `B`.

## Definition

### Complements of De Morgan subtypes

```agda
complement-de-morgan-subtype :
  {l1 l2 : Level} {A : UU l1} → de-morgan-subtype l2 A → de-morgan-subtype l2 A
complement-de-morgan-subtype P x = neg-De-Morgan-Prop (P x)
```

## Properties

### Complement of De Morgan subtypes are decidable

```agda
is-decidable-complement-de-morgan-subtype :
  {l1 l2 : Level} {A : UU l1} (P : de-morgan-subtype l2 A) →
  is-decidable-subtype
    ( subtype-de-morgan-subtype (complement-de-morgan-subtype P))
is-decidable-complement-de-morgan-subtype P = is-de-morgan-de-morgan-subtype P
```

### The union of the complement of a subtype `P` with its double complement is the full subtype if and only if `P` is De Morgan

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  is-full-union-complement-subtype-double-complement-subtype :
    (P : subtype l2 A) → is-de-morgan-subtype P →
    is-full-subtype
      ( union-subtype
        ( complement-subtype P)
        ( complement-subtype (complement-subtype P)))
  is-full-union-complement-subtype-double-complement-subtype P =
    is-full-union-subtype-complement-subtype (complement-subtype P)

  is-de-morgan-subtype-is-full-union-complement-subtype-double-complement-subtype :
    (P : subtype l2 A) →
    is-full-subtype
      ( union-subtype
        ( complement-subtype P)
        ( complement-subtype (complement-subtype P))) →
    is-de-morgan-subtype P
  is-de-morgan-subtype-is-full-union-complement-subtype-double-complement-subtype
    P =
    is-decidable-subtype-is-full-union-subtype-complement-subtype
      ( complement-subtype P)

  is-full-union-subtype-complement-de-morgan-subtype :
    (P : de-morgan-subtype l2 A) →
    is-full-subtype
      ( union-de-morgan-subtype P (complement-de-morgan-subtype P))
  is-full-union-subtype-complement-de-morgan-subtype P =
    is-full-union-complement-subtype-double-complement-subtype
      ( subtype-de-morgan-subtype P)
      ( is-de-morgan-de-morgan-subtype P)
```
