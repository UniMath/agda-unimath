# Preimages of subtypes

```agda
module foundation.preimages-of-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.subtypes
```

</details>

## Idea

The {{#concept "preimage" Disambiguation="of a subtype" Agda=preimage-subtype}}
of a [subtype](foundation-core.subtypes.md) `S ⊆ B` under a map `f : A → B` is
the subtype of `A` consisting of elements `a` such that `f a ∈ S`.

## Definition

```agda
preimage-subtype :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  subtype l3 B → subtype l3 A
preimage-subtype f S a = S (f a)
```
