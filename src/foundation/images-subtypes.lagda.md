# Images of subtypes

```agda
module foundation.images-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.images
open import foundation.logical-equivalences
open import foundation.powersets
open import foundation.propositional-truncations
open import foundation.pullbacks-subtypes
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.subtypes

open import order-theory.galois-connections-large-posets
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
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
  image-subtype f ⊣ pullback-subtype f
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

### The order preserving operation taking the image of a subtype under a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  preserves-order-im-subtype :
    {l3 l4 : Level} (S : subtype l3 A) (T : subtype l4 A) →
    S ⊆ T → im-subtype f S ⊆ im-subtype f T
  preserves-order-im-subtype S T H y p =
    apply-universal-property-trunc-Prop p
      ( im-subtype f T y)
      ( λ ((x , s) , q) → unit-trunc-Prop ((x , H x s) , q))

  im-subtype-hom-Large-Poset :
    hom-Large-Poset
      ( λ l → l1 ⊔ l2 ⊔ l)
      ( powerset-Large-Poset A)
      ( powerset-Large-Poset B)
  map-hom-Large-Preorder im-subtype-hom-Large-Poset =
    im-subtype f
  preserves-order-hom-Large-Preorder im-subtype-hom-Large-Poset =
    preserves-order-im-subtype
```

### The image-pullback Galois connection on powersets

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  forward-implication-adjoint-relation-image-pullback-subtype :
    {l3 l4 : Level} (S : subtype l3 A) (T : subtype l4 B) →
    (im-subtype f S ⊆ T) → (S ⊆ pullback-subtype f T)
  forward-implication-adjoint-relation-image-pullback-subtype S T H x p =
    H (f x) (unit-trunc-Prop ((x , p) , refl))

  backward-implication-adjoint-relation-image-pullback-subtype :
    {l3 l4 : Level} (S : subtype l3 A) (T : subtype l4 B) →
    (S ⊆ pullback-subtype f T) → (im-subtype f S ⊆ T)
  backward-implication-adjoint-relation-image-pullback-subtype S T H y p =
    apply-universal-property-trunc-Prop p
      ( T y)
      ( λ where ((x , s) , refl) → H x s)

  adjoint-relation-image-pullback-subtype :
    {l3 l4 : Level} (S : subtype l3 A) (T : subtype l4 B) →
    (im-subtype f S ⊆ T) ↔ (S ⊆ pullback-subtype f T)
  pr1 (adjoint-relation-image-pullback-subtype S T) =
    forward-implication-adjoint-relation-image-pullback-subtype S T
  pr2 (adjoint-relation-image-pullback-subtype S T) =
    backward-implication-adjoint-relation-image-pullback-subtype S T

  image-pullback-subtype-galois-connection-Large-Poset :
    galois-connection-Large-Poset
      ( λ l → l1 ⊔ l2 ⊔ l)
      ( λ l → l)
      ( powerset-Large-Poset A)
      ( powerset-Large-Poset B)
  lower-adjoint-galois-connection-Large-Poset
    image-pullback-subtype-galois-connection-Large-Poset =
    im-subtype-hom-Large-Poset f
  upper-adjoint-galois-connection-Large-Poset
    image-pullback-subtype-galois-connection-Large-Poset =
    pullback-subtype-hom-Large-Poset f
  adjoint-relation-galois-connection-Large-Poset
    image-pullback-subtype-galois-connection-Large-Poset =
    adjoint-relation-image-pullback-subtype
```
