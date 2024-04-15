# Pullbacks of subtypes

```agda
module foundation.pullbacks-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.logical-equivalences
open import foundation.powersets
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.propositions
open import foundation-core.subtypes

open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
```

</details>

## Idea

Consider a [subtype](foundation-core.subtypes.md) `T` of a type `B` and a map
`f : A → B`. Then the {{#concept "pullback subtype" Agda=pullback-subtype}}
`pullback f T` of `A` is defined to be `T ∘ f`. This fits in a
[pullback diagram](foundation-core.pullbacks.md)

```text
                 π₂
  pullback f T -----> T
       | ⌟            |
    π₁ |              | i
       |              |
       V              V
       A -----------> B
               f
```

The
[universal property of pullbacks](foundation.universal-property-pullbacks.md)
quite literally returns the definition of the subtype `pullback f T`, because it
essentially asserts that

```text
  (S ⊆ pullback f T) ↔ ((x : A) → is-in-subtype S x → is-in-subtype T (f x)).
```

The operation `pullback f : subtype B → subtype A` is an
[order preserving map](order-theory.order-preserving-maps-large-posets.md)
between the [powersets](foundation.powersets.md) of `B` and `A`.

In the file [Images of subtypes](foundation.images-subtypes.md) we show that the
pullback operation on subtypes is the upper adjoint of a
[Galois connection](order-theory.galois-connections-large-posets.md).

## Definitions

### The predicate of being a pullback of subtypes

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (T : subtype l3 B) (S : subtype l4 A)
  where

  is-pullback-subtype : UUω
  is-pullback-subtype =
    {l : Level} (U : subtype l A) →
    (U ⊆ S) ↔ ((x : A) → is-in-subtype U x → is-in-subtype T (f x))
```

### Pullbacks of subtypes

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (T : subtype l3 B)
  where

  pullback-subtype : subtype l3 A
  pullback-subtype = T ∘ f

  is-in-pullback-subtype : A → UU l3
  is-in-pullback-subtype = is-in-subtype pullback-subtype

  is-prop-is-in-pullback-subtype :
    (x : A) → is-prop (is-in-pullback-subtype x)
  is-prop-is-in-pullback-subtype = is-prop-is-in-subtype pullback-subtype

  type-pullback-subtype : UU (l1 ⊔ l3)
  type-pullback-subtype = type-subtype pullback-subtype

  inclusion-pullback-subtype : type-pullback-subtype → A
  inclusion-pullback-subtype = inclusion-subtype pullback-subtype
```

### The order preserving pullback operation on subtypes

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  preserves-order-pullback-subtype :
    preserves-order-map-Large-Poset
      ( powerset-Large-Poset B)
      ( powerset-Large-Poset A)
      ( pullback-subtype f)
  preserves-order-pullback-subtype S T H x = H (f x)

  pullback-subtype-hom-Large-Poset :
    hom-Large-Poset (λ l → l) (powerset-Large-Poset B) (powerset-Large-Poset A)
  map-hom-Large-Preorder pullback-subtype-hom-Large-Poset =
    pullback-subtype f
  preserves-order-hom-Large-Preorder pullback-subtype-hom-Large-Poset =
    preserves-order-pullback-subtype
```

## See also

- The [image of a subtype](foundation.images-subtypes.md)
