# Complements of double negation stable subtypes

```agda
module logic.complements-double-negation-stable-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.double-negation-stable-propositions
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

open import logic.double-negation-stable-subtypes
```

</details>

## Idea

The
{{#concept "complement" Disambiguation="of a double negation stable subtype" Agda=complement-double-negation-stable-subtype}}
of a [double negation stable subtype](logic.double-negation-stable-subtypes.md)
`B ⊆ A` consists of the elements that are not in `B`.

## Definition

### Complements of double negation stable subtypes

```agda
complement-double-negation-stable-subtype :
  {l1 l2 : Level} {A : UU l1} →
  double-negation-stable-subtype l2 A →
  double-negation-stable-subtype l2 A
complement-double-negation-stable-subtype P x =
  neg-Double-Negation-Stable-Prop (P x)
```

## Properties

### Taking complements is an involution on double negation stable subtypes

```agda
is-involution-complement-double-negation-stable-subtype :
  {l1 l2 : Level} {A : UU l1} →
  is-involution (complement-double-negation-stable-subtype {l1} {l2} {A})
is-involution-complement-double-negation-stable-subtype P =
  eq-has-same-elements-double-negation-stable-subtype
    ( complement-double-negation-stable-subtype
      ( complement-double-negation-stable-subtype P))
    ( P)
    ( λ x →
      ( is-double-negation-stable-double-negation-stable-subtype P x ,
        intro-double-negation))
```
