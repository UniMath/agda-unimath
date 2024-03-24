# Set presented types

```agda
module foundation.set-presented-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.set-truncations
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

A type `A` is said to be
{{#concept "set presented" Agda=has-set-presentation-Prop}} if there
[exists](foundation.existential-quantification.md) a map `f : X → A` from a
[set](foundation-core.sets.md) `X` such that the composite
`X → A → type-trunc-Set A` is an [equivalence](foundation.equivalences.md).

```agda
module _
  {l1 l2 : Level} (A : Set l1) (B : UU l2)
  where

  has-set-presentation-Prop : Prop (l1 ⊔ l2)
  has-set-presentation-Prop =
    ∃ (type-Set A → B) (λ f → is-equiv-Prop (unit-trunc-Set ∘ f))
```
