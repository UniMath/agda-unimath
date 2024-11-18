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
```

</details>

## Idea

The
{{#concept "complement" Disambiguation="of a subtype" Agda=complement-subtype}}
of a [subtype](foundation-core.subtypes.md) `P ⊆ A` consists of the elements
that are not in `P`.

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
