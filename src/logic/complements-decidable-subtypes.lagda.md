# Complements of decidable subtypes

```agda
module logic.complements-decidable-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.complements-subtypes
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.equivalences
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation-stable-propositions
open import foundation.evaluation-functions
open import foundation.full-subtypes
open import foundation.involutions
open import foundation.disjoint-subtypes
open import foundation.negation
open import foundation.postcomposition-functions
open import foundation.powersets
open import foundation.propositional-truncations
open import foundation.unions-subtypes
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.subtypes

open import logic.double-negation-stable-subtypes
```

</details>

## Idea

The
{{#concept "complement" Disambiguation="of a decidable subtype" Agda=complement-decidable-subtype}}
of a [decidable subtype](foundation.decidable-subtypes.md) `B ⊆ A` consists of
the elements that are not in `B`.

## Definition

### Complements of decidable subtypes

```agda
complement-decidable-subtype :
  {l1 l2 : Level} {A : UU l1} → decidable-subtype l2 A → decidable-subtype l2 A
complement-decidable-subtype P x = neg-Decidable-Prop (P x)
```

## Properties

### The complement of a decidable subtype is disjoint from the subtype

```agda
disjoint-complement-decidable-subtype :
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A) →
  disjoint-decidable-subtype P (complement-decidable-subtype P)
disjoint-complement-decidable-subtype P =
  disjoint-complement-subtype (subtype-decidable-subtype P)
```

### Taking complements is an involution on decidable subtypes

```agda
is-involution-complement-decidable-subtype :
  {l1 l2 : Level} {A : UU l1} →
  is-involution (complement-decidable-subtype {l1} {l2} {A})
is-involution-complement-decidable-subtype P =
  eq-has-same-elements-decidable-subtype
    ( complement-decidable-subtype (complement-decidable-subtype P))
    ( P)
    ( λ x →
      double-negation-elim-is-decidable (is-decidable-decidable-subtype P x) ,
      ev)
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

### `A` is equivalent to the coproduct of a decidable subtype and its complement

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where

  equiv-coproduct-subtype-complement-decidable-subtype :
    A ≃
    type-decidable-subtype P +
    type-decidable-subtype (complement-decidable-subtype P)
  equiv-coproduct-subtype-complement-decidable-subtype =
    equiv-union-coproduct-disjoint-subtype
      ( subtype-decidable-subtype P)
      ( subtype-decidable-subtype (complement-decidable-subtype P))
      ( disjoint-complement-decidable-subtype P) ∘e
    inv-equiv
      ( equiv-inclusion-is-full-subtype
        ( subtype-decidable-subtype
          ( union-decidable-subtype P (complement-decidable-subtype P)))
        ( is-full-union-subtype-complement-decidable-subtype P))
```
