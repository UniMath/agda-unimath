# Images of semigroup homomorphisms

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.images-of-semigroup-homomorphisms
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.images funext
open import foundation.images funext-subtypes
open import foundation.logical-equivalences funext
open import foundation.propositional-truncations funext
open import foundation.universal-property-image funext
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups funext
open import group-theory.pullbacks-subsemigroups funext
open import group-theory.semigroups funext
open import group-theory.subsemigroups funext
open import group-theory.subsets-semigroups funext

open import order-theory.galois-connections-large-posets funext
open import order-theory.order-preserving-maps-large-posets funext
open import order-theory.order-preserving-maps-large-preorders funext
```

</details>

## Idea

The **image** of a
[semigroup homomorphism](group-theory.homomorphisms-semigroups.md) `f : G → H`
consists of the [image](foundation.images.md) of the underlying map of `f`. This
[subset](group-theory.subsets-semigroups.md) is closed under multiplication, so
it is a [subsemigroup](group-theory.subsemigroups.md) of the
[semigroup](group-theory.semigroups.md) `H`. Alternatively, it can be described
as the least subsemigroup of `H` that contains all the values of `f`.

More generally, the **image of a subsemigroup** `S` under a semigroup
homomorphism `f : G → H` is the subsemigroup consisting of all the elements in
the image of the underlying [subset](foundation-core.subtypes.md) of `S` under
the underlying map of `f`. Since the image of a subsemigroup satisfies the
following adjoint relation

```text
  (im f S ⊆ T) ↔ (S ⊆ T ∘ f)
```

it follows that we obtain a
[Galois connection](order-theory.galois-connections.md).

## Definitions

### The universal property of the image of a semigroup homomorphism

```agda
module _
  {l1 l2 l3 : Level} (G : Semigroup l1) (H : Semigroup l2)
  (f : hom-Semigroup G H) (K : Subsemigroup l3 H)
  where

  is-image-hom-Semigroup : UUω
  is-image-hom-Semigroup =
    {l : Level} (L : Subsemigroup l H) →
    leq-Subsemigroup H K L ↔
    ( (g : type-Semigroup G) →
      is-in-Subsemigroup H L (map-hom-Semigroup G H f g))
```

### The universal property of the image subsemigroup of a subsemigroup

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Semigroup l1) (H : Semigroup l2)
  (f : hom-Semigroup G H) (S : Subsemigroup l3 G) (T : Subsemigroup l4 H)
  where

  is-image-subsemigroup-hom-Semigroup : UUω
  is-image-subsemigroup-hom-Semigroup =
    {l : Level} (U : Subsemigroup l H) →
    leq-Subsemigroup H T U ↔
    leq-Subsemigroup G S (pullback-Subsemigroup G H f U)
```

### The image subsemigroup under a semigroup homomorphism

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2) (f : hom-Semigroup G H)
  where

  subset-image-hom-Semigroup : subset-Semigroup (l1 ⊔ l2) H
  subset-image-hom-Semigroup = subtype-im (map-hom-Semigroup G H f)

  is-image-subtype-subset-image-hom-Semigroup :
    is-image-subtype (map-hom-Semigroup G H f) subset-image-hom-Semigroup
  is-image-subtype-subset-image-hom-Semigroup =
    is-image-subtype-subtype-im (map-hom-Semigroup G H f)

  abstract
    is-closed-under-multiplication-image-hom-Semigroup :
      is-closed-under-multiplication-subset-Semigroup H
        subset-image-hom-Semigroup
    is-closed-under-multiplication-image-hom-Semigroup {x} {y} K L =
      apply-twice-universal-property-trunc-Prop K L
        ( subset-image-hom-Semigroup (mul-Semigroup H x y))
        ( λ where
          ( g , refl) (h , refl) →
            unit-trunc-Prop
              ( mul-Semigroup G g h , preserves-mul-hom-Semigroup G H f))

  image-hom-Semigroup : Subsemigroup (l1 ⊔ l2) H
  pr1 image-hom-Semigroup = subset-image-hom-Semigroup
  pr2 image-hom-Semigroup = is-closed-under-multiplication-image-hom-Semigroup

  is-image-image-hom-Semigroup :
    is-image-hom-Semigroup G H f image-hom-Semigroup
  is-image-image-hom-Semigroup K =
    is-image-subtype-subset-image-hom-Semigroup (subset-Subsemigroup H K)

  contains-values-image-hom-Semigroup :
    (g : type-Semigroup G) →
    is-in-Subsemigroup H image-hom-Semigroup (map-hom-Semigroup G H f g)
  contains-values-image-hom-Semigroup =
    forward-implication
      ( is-image-image-hom-Semigroup image-hom-Semigroup)
      ( refl-leq-Subsemigroup H image-hom-Semigroup)

  leq-image-hom-Semigroup :
    {l : Level} (K : Subsemigroup l H) →
    ( ( g : type-Semigroup G) →
      is-in-Subsemigroup H K (map-hom-Semigroup G H f g)) →
    leq-Subsemigroup H image-hom-Semigroup K
  leq-image-hom-Semigroup K =
    backward-implication (is-image-image-hom-Semigroup K)
```

### The image of a subsemigroup under a semigroup homomorphism

```agda
module _
  {l1 l2 l3 : Level} (G : Semigroup l1) (H : Semigroup l2)
  (f : hom-Semigroup G H) (K : Subsemigroup l3 G)
  where

  subset-im-hom-Subsemigroup : subset-Semigroup (l1 ⊔ l2 ⊔ l3) H
  subset-im-hom-Subsemigroup =
    im-subtype (map-hom-Semigroup G H f) (subset-Subsemigroup G K)

  abstract
    is-closed-under-multiplication-im-hom-Subsemigroup :
      is-closed-under-multiplication-subset-Semigroup H
        subset-im-hom-Subsemigroup
    is-closed-under-multiplication-im-hom-Subsemigroup {x} {y} u v =
      apply-twice-universal-property-trunc-Prop u v
        ( subset-im-hom-Subsemigroup (mul-Semigroup H x y))
        ( λ where
          ((x' , k) , refl) ((y' , l) , refl) →
            unit-trunc-Prop
              ( ( mul-Subsemigroup G K (x' , k) (y' , l)) ,
                ( preserves-mul-hom-Semigroup G H f)))

  im-hom-Subsemigroup : Subsemigroup (l1 ⊔ l2 ⊔ l3) H
  pr1 im-hom-Subsemigroup =
    subset-im-hom-Subsemigroup
  pr2 im-hom-Subsemigroup =
    is-closed-under-multiplication-im-hom-Subsemigroup

  forward-implication-is-image-subsemigroup-im-hom-Subsemigroup :
    {l : Level} (U : Subsemigroup l H) →
    leq-Subsemigroup H im-hom-Subsemigroup U →
    leq-Subsemigroup G K (pullback-Subsemigroup G H f U)
  forward-implication-is-image-subsemigroup-im-hom-Subsemigroup U =
    forward-implication-adjoint-relation-image-pullback-subtype
      ( map-hom-Semigroup G H f)
      ( subset-Subsemigroup G K)
      ( subset-Subsemigroup H U)

  backward-implication-is-image-subsemigroup-im-hom-Subsemigroup :
    {l : Level} (U : Subsemigroup l H) →
    leq-Subsemigroup G K (pullback-Subsemigroup G H f U) →
    leq-Subsemigroup H im-hom-Subsemigroup U
  backward-implication-is-image-subsemigroup-im-hom-Subsemigroup U =
    backward-implication-adjoint-relation-image-pullback-subtype
      ( map-hom-Semigroup G H f)
      ( subset-Subsemigroup G K)
      ( subset-Subsemigroup H U)

  is-image-subsemigroup-im-hom-Subsemigroup :
    is-image-subsemigroup-hom-Semigroup G H f K im-hom-Subsemigroup
  is-image-subsemigroup-im-hom-Subsemigroup U =
    adjoint-relation-image-pullback-subtype
      ( map-hom-Semigroup G H f)
      ( subset-Subsemigroup G K)
      ( subset-Subsemigroup H U)
```

### The image-pullback Galois connection on subsemigroups

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2) (f : hom-Semigroup G H)
  where

  preserves-order-im-hom-Subsemigroup :
    {l3 l4 : Level} (K : Subsemigroup l3 G) (L : Subsemigroup l4 G) →
    leq-Subsemigroup G K L →
    leq-Subsemigroup H
      ( im-hom-Subsemigroup G H f K)
      ( im-hom-Subsemigroup G H f L)
  preserves-order-im-hom-Subsemigroup K L =
    preserves-order-im-subtype
      ( map-hom-Semigroup G H f)
      ( subset-Subsemigroup G K)
      ( subset-Subsemigroup G L)

  im-hom-subsemigroup-hom-Large-Poset :
    hom-Large-Poset
      ( λ l → l1 ⊔ l2 ⊔ l)
      ( Subsemigroup-Large-Poset G)
      ( Subsemigroup-Large-Poset H)
  map-hom-Large-Preorder im-hom-subsemigroup-hom-Large-Poset =
    im-hom-Subsemigroup G H f
  preserves-order-hom-Large-Preorder im-hom-subsemigroup-hom-Large-Poset =
    preserves-order-im-hom-Subsemigroup

  image-pullback-galois-connection-Subsemigroup :
    galois-connection-Large-Poset
      ( λ l → l1 ⊔ l2 ⊔ l)
      ( λ l → l)
      ( Subsemigroup-Large-Poset G)
      ( Subsemigroup-Large-Poset H)
  lower-adjoint-galois-connection-Large-Poset
    image-pullback-galois-connection-Subsemigroup =
    im-hom-subsemigroup-hom-Large-Poset
  upper-adjoint-galois-connection-Large-Poset
    image-pullback-galois-connection-Subsemigroup =
    pullback-hom-large-poset-Subsemigroup G H f
  adjoint-relation-galois-connection-Large-Poset
    image-pullback-galois-connection-Subsemigroup K =
    is-image-subsemigroup-im-hom-Subsemigroup G H f K
```
