# Isomorphisms of monoids

```agda
module group-theory.isomorphisms-monoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories

open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.homomorphisms-monoids
open import group-theory.invertible-elements-monoids
open import group-theory.monoids
open import group-theory.precategory-of-monoids
```

</details>

## Idea

An **isomorphism** of [monoids](group-theory.monoids.md) is an invertible
[homomorphism of monoids](group-theory.homomorphisms-monoids.md).

## Definitions

### The predicate of being an isomorphism

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2) (f : hom-Monoid M N)
  where

  is-iso-Monoid : UU (l1 ⊔ l2)
  is-iso-Monoid =
    is-iso-Large-Precategory Monoid-Large-Precategory {X = M} {Y = N} f

  hom-inv-is-iso-Monoid :
    is-iso-Monoid → hom-Monoid N M
  hom-inv-is-iso-Monoid =
    hom-inv-is-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      ( f)

  is-section-hom-inv-is-iso-Monoid :
    (H : is-iso-Monoid) →
    comp-hom-Monoid N M N f (hom-inv-is-iso-Monoid H) ＝
    id-hom-Monoid N
  is-section-hom-inv-is-iso-Monoid =
    is-section-hom-inv-is-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      ( f)

  is-retraction-hom-inv-is-iso-Monoid :
    (H : is-iso-Monoid) →
    comp-hom-Monoid M N M (hom-inv-is-iso-Monoid H) f ＝
    id-hom-Monoid M
  is-retraction-hom-inv-is-iso-Monoid =
    is-retraction-hom-inv-is-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      ( f)
```

### Isomorphisms of monoids

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  iso-Monoid : UU (l1 ⊔ l2)
  iso-Monoid =
    iso-Large-Precategory Monoid-Large-Precategory M N

  hom-iso-Monoid :
    iso-Monoid → hom-Monoid M N
  hom-iso-Monoid =
    hom-iso-Large-Precategory Monoid-Large-Precategory {X = M} {Y = N}

  map-iso-Monoid :
    iso-Monoid → type-Monoid M → type-Monoid N
  map-iso-Monoid f = map-hom-Monoid M N (hom-iso-Monoid f)

  preserves-mul-iso-Monoid :
    (f : iso-Monoid) {x y : type-Monoid M} →
    map-iso-Monoid f (mul-Monoid M x y) ＝
    mul-Monoid N (map-iso-Monoid f x) (map-iso-Monoid f y)
  preserves-mul-iso-Monoid f =
    preserves-mul-hom-Monoid M N (hom-iso-Monoid f)

  is-iso-iso-Monoid :
    (f : iso-Monoid) →
    is-iso-Monoid M N (hom-iso-Monoid f)
  is-iso-iso-Monoid =
    is-iso-iso-Large-Precategory Monoid-Large-Precategory {X = M} {Y = N}

  hom-inv-iso-Monoid :
    iso-Monoid → hom-Monoid N M
  hom-inv-iso-Monoid =
    hom-inv-iso-Large-Precategory Monoid-Large-Precategory {X = M} {Y = N}

  map-inv-iso-Monoid :
    iso-Monoid → type-Monoid N → type-Monoid M
  map-inv-iso-Monoid f =
    map-hom-Monoid N M (hom-inv-iso-Monoid f)

  preserves-mul-inv-iso-Monoid :
    (f : iso-Monoid) {x y : type-Monoid N} →
    map-inv-iso-Monoid f (mul-Monoid N x y) ＝
    mul-Monoid M (map-inv-iso-Monoid f x) (map-inv-iso-Monoid f y)
  preserves-mul-inv-iso-Monoid f =
    preserves-mul-hom-Monoid N M (hom-inv-iso-Monoid f)

  is-section-hom-inv-iso-Monoid :
    (f : iso-Monoid) →
    comp-hom-Monoid N M N (hom-iso-Monoid f) (hom-inv-iso-Monoid f) ＝
    id-hom-Monoid N
  is-section-hom-inv-iso-Monoid =
    is-section-hom-inv-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}

  is-section-map-inv-iso-Monoid :
    (f : iso-Monoid) →
    map-iso-Monoid f ∘ map-inv-iso-Monoid f ~ id
  is-section-map-inv-iso-Monoid f =
    htpy-eq-hom-Monoid N N
      ( comp-hom-Monoid N M N (hom-iso-Monoid f) (hom-inv-iso-Monoid f))
      ( id-hom-Monoid N)
      ( is-section-hom-inv-iso-Monoid f)

  is-retraction-hom-inv-iso-Monoid :
    (f : iso-Monoid) →
    comp-hom-Monoid M N M (hom-inv-iso-Monoid f) (hom-iso-Monoid f) ＝
    id-hom-Monoid M
  is-retraction-hom-inv-iso-Monoid =
    is-retraction-hom-inv-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}

  is-retraction-map-inv-iso-Monoid :
    (f : iso-Monoid) →
    map-inv-iso-Monoid f ∘ map-iso-Monoid f ~ id
  is-retraction-map-inv-iso-Monoid f =
    htpy-eq-hom-Monoid M M
      ( comp-hom-Monoid M N M (hom-inv-iso-Monoid f) (hom-iso-Monoid f))
      ( id-hom-Monoid M)
      ( is-retraction-hom-inv-iso-Monoid f)
```

## Examples

### Identity homomorphisms are isomorphisms

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-iso-id-hom-Monoid :
    is-iso-Monoid M M (id-hom-Monoid M)
  is-iso-id-hom-Monoid =
    is-iso-id-hom-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}

  id-iso-Monoid : iso-Monoid M M
  id-iso-Monoid =
    id-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
```

### Equalities induce isomorphisms

An equality between objects `x y : A` gives rise to an isomorphism between them.
This is because by the J-rule, it is enough to construct an isomorphism given
`refl : x ＝ x`, from `x` to itself. We take the identity morphism as such an
isomorphism.

```agda
iso-eq-Monoid :
  {l1 : Level} (M N : Monoid l1) → M ＝ N → iso-Monoid M N
iso-eq-Monoid = iso-eq-Large-Precategory Monoid-Large-Precategory
```

## Properties

### Being an isomorphism is a proposition

Let `f : hom x y` and suppose `g g' : hom y x` are both two-sided inverses to
`f`. It is enough to show that `g = g'` since the equalities are propositions
(since the hom-types are sets). But we have the following chain of equalities:
`g = g ∘ id_y = g ∘ (f ∘ g') = (g ∘ f) ∘ g' = id_x ∘ g' = g'`.

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  is-prop-is-iso-Monoid :
    (f : hom-Monoid M N) →
    is-prop (is-iso-Monoid M N f)
  is-prop-is-iso-Monoid =
    is-prop-is-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}
  is-iso-prop-Monoid :
    (f : hom-Monoid M N) → Prop (l1 ⊔ l2)
  is-iso-prop-Monoid =
    is-iso-prop-Large-Precategory Monoid-Large-Precategory {X = M} {Y = N}
```

### The type of isomorphisms form a set

The type of isomorphisms between objects `x y : A` is a subtype of the set
`hom x y` since being an isomorphism is a proposition.

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  is-set-iso-Monoid : is-set (iso-Monoid M N)
  is-set-iso-Monoid =
    is-set-iso-Large-Precategory Monoid-Large-Precategory {X = M} {Y = N}

  iso-set-Monoid : Set (l1 ⊔ l2)
  iso-set-Monoid =
    iso-set-Large-Precategory Monoid-Large-Precategory {X = M} {Y = N}
```

### Isomorphisms are stable by composition

```agda
module _
  {l1 l2 l3 : Level} (M : Monoid l1) (N : Monoid l2) (K : Monoid l3)
  (g : iso-Monoid N K) (f : iso-Monoid M N)
  where

  hom-comp-iso-Monoid : hom-Monoid M K
  hom-comp-iso-Monoid =
    hom-comp-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      { Z = K}
      ( g)
      ( f)

  is-iso-comp-iso-Monoid :
    is-iso-Monoid M K hom-comp-iso-Monoid
  is-iso-comp-iso-Monoid =
    is-iso-comp-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      { Z = K}
      ( g)
      ( f)

  comp-iso-Monoid : iso-Monoid M K
  comp-iso-Monoid =
    comp-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      { Z = K}
      ( g)
      ( f)
```

### Inverses of isomorphisms are isomorphisms

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2) (f : iso-Monoid M N)
  where

  is-iso-inv-iso-Monoid :
    is-iso-Monoid N M (hom-inv-iso-Monoid M N f)
  is-iso-inv-iso-Monoid =
    is-iso-inv-is-iso-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      ( is-iso-iso-Monoid M N f)

  inv-iso-Monoid : iso-Monoid N M
  inv-iso-Monoid =
    inv-iso-Large-Precategory Monoid-Large-Precategory {X = M} {Y = N} f
```

### Any isomorphism of monoids preserves and reflects invertible elements

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  (f : iso-Monoid M N)
  where

  preserves-invertible-elements-iso-Monoid :
    {x : type-Monoid M} →
    is-invertible-element-Monoid M x →
    is-invertible-element-Monoid N (map-iso-Monoid M N f x)
  preserves-invertible-elements-iso-Monoid =
    preserves-invertible-elements-hom-Monoid M N (hom-iso-Monoid M N f)

  reflects-invertible-elements-iso-Monoid :
    {x : type-Monoid M} →
    is-invertible-element-Monoid N (map-iso-Monoid M N f x) →
    is-invertible-element-Monoid M x
  reflects-invertible-elements-iso-Monoid H =
    tr
      ( is-invertible-element-Monoid M)
      ( is-retraction-map-inv-iso-Monoid M N f _)
      ( preserves-invertible-elements-hom-Monoid N M
        ( hom-inv-iso-Monoid M N f)
        ( H))
```
