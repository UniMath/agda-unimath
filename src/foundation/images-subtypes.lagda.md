# Images of subtypes

```agda
module foundation.images-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.images
open import foundation.logical-equivalences
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.subtypes
```

</details>

## Idea

Consider a map `f : A → B` and a [subtype](foundation-core.subtypes.md) `S ⊆ A`,
then the **image** of `S` under `f` is the subtype of `B` consisting of the
values of the composite `S ⊆ A → B`. In other words, the image `im f S` of a
subtype `S` under `f` satisfies the universal property that

```text
  (im f S ⊆ U) ↔ (S ⊆ U ∘ f).
```

The image operation on subtypes is of course an
[order preserving map](order-theory.order-preserving-maps-large-posets.md) of
[large posets](order-theory.large-posets.md), and by the above universal
property we obtain a
[galois connection](order-theory.galois-connections-large-posets.md)

```text
  im f ⊣ precomp f
```

## Definition

### The predicate of being the image of a subtype under a map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (S : subtype l3 A)
  where

  is-image-map-subtype : {l4 : Level} (T : subtype l4 B) → UUω
  is-image-map-subtype T =
    {l : Level} (U : subtype l B) → (T ⊆ U) ↔ (S ⊆ U ∘ f)
```

### The image of a subtype under a map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (S : subtype l3 A)
  where

  im-subtype : subtype (l1 ⊔ l2 ⊔ l3) B
  im-subtype y = subtype-im (f ∘ inclusion-subtype S) y
```
