# Set presented types

```agda
module foundation.set-presented-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.functions
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

A type `A` is said to be set presented if there exists a map `f : X → A` from a set `X` such that the composite `X → A → type-trunc-Set A` is an equivalence.

```agda
has-set-presentation-Prop :
  {l1 l2 : Level} (A : Set l1) (B : UU l2) → Prop (l1 ⊔ l2)
has-set-presentation-Prop A B =
  ∃-Prop (type-Set A → B) (λ f → is-equiv (unit-trunc-Set ∘ f))
```
