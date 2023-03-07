# Preimages of subtypes

```agda
module foundation.preimages-of-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

The preimage of a subtype `S ⊆ B` under a map `f : A → B` is the subtype of `A` consisting of elements `a` such that `f a ∈ S`.

## Definition

```agda
preimage-subtype :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  subtype l3 B → subtype l3 A
preimage-subtype f S a = S (f a)
```
