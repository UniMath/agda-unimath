# Complements of De Morgan subtypes

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module logic.complements-de-morgan-subtypes
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.complements-subtypes funext univalence truncations
open import foundation.decidable-subtypes funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.double-negation funext univalence truncations
open import foundation.full-subtypes funext univalence truncations
open import foundation.involutions funext univalence
open import foundation.negation funext
open import foundation.postcomposition-functions funext
open import foundation.powersets funext univalence truncations
open import foundation.propositional-truncations funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.unions-subtypes funext univalence truncations
open import foundation.universe-levels

open import foundation-core.function-types

open import logic.complements-decidable-subtypes funext univalence truncations
open import logic.de-morgan-propositions funext univalence truncations
open import logic.de-morgan-subtypes funext univalence truncations
```

</details>

## Idea

The
{{#concept "complement" Disambiguation="of a De Morgan subtype" Agda=complement-de-morgan-subtype}}
of a [De Morgan subtype](logic.de-morgan-subtypes.md) `B ⊆ A` consists of the
elements that are not in `B`.

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
      ( union-subtype
        ( complement-subtype (subtype-de-morgan-subtype P))
        ( complement-subtype
          ( complement-subtype (subtype-de-morgan-subtype P))))
  is-full-union-subtype-complement-de-morgan-subtype P =
    is-full-union-complement-subtype-double-complement-subtype
      ( subtype-de-morgan-subtype P)
      ( is-de-morgan-de-morgan-subtype P)
```
