# Images of subtypes

```agda
module foundation.images-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.images
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.univalence
open import foundation.universe-levels
```

</details>

## Idea

Consider a map `f : A → B` and a subtype `S ⊆ A`, then the images of `S` under
`f` is the subtype of `B` consisting of the values of the composite `S ⊆ A → B`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  subtype-im-subtype :
    {l3 : Level} → subtype l3 A → subtype (l1 ⊔ l2 ⊔ l3) B
  subtype-im-subtype S y = subtype-im (f ∘ inclusion-subtype S) y
```
