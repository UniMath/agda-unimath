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
of a [subtype](foundation-core.subtypes.md) `P` of `A` consists of the elements
that are not in `P`.

## Definition

### Complements of subtypes

```agda
complement-subtype :
  {l1 l2 : Level} {A : UU l1} → subtype l2 A → subtype l2 A
complement-subtype P x = neg-Prop (P x)
```

### Complements of decidable subtypes

```agda
complement-decidable-subtype :
  {l1 l2 : Level} {A : UU l1} → decidable-subtype l2 A → decidable-subtype l2 A
complement-decidable-subtype P x = neg-Decidable-Prop (P x)
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

### The union of a subtype `P` with its complement is the full subtype if and only if `P` is a decidable subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  is-full-union-subtype-complement-subtype :
    (P : subtype l2 A) → is-decidable-subtype P →
    is-full-subtype (union-subtype P (complement-subtype P))
  is-full-union-subtype-complement-subtype P d x =
    unit-trunc-Prop (d x)

  is-decidable-subtype-is-full-union-subtype-complement-subtype :
    (P : subtype l2 A) →
    is-full-subtype (union-subtype P (complement-subtype P)) →
    is-decidable-subtype P
  is-decidable-subtype-is-full-union-subtype-complement-subtype P H x =
    apply-universal-property-trunc-Prop
      ( H x)
      ( is-decidable-Prop (P x))
      ( id)

  is-full-union-subtype-complement-decidable-subtype :
    (P : decidable-subtype l2 A) →
    is-full-decidable-subtype
      ( union-decidable-subtype P (complement-decidable-subtype P))
  is-full-union-subtype-complement-decidable-subtype P =
    is-full-union-subtype-complement-subtype
      ( subtype-decidable-subtype P)
      ( is-decidable-decidable-subtype P)
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
