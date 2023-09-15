# Isomorphisms of monoids

```agda
module group-theory.isomorphisms-monoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories

open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.homomorphisms-monoids
open import group-theory.monoids
open import group-theory.precategory-of-monoids
```

</details>

## Idea

An **isomorphism** of [monoids](group-theory.monoids.md) is an invertible [homomorphism of monoids](group-theory.homomorphisms-monoids.md).

## Definitions

### The predicate of being an isomorphism

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2) (f : type-hom-Monoid M N)
  where

  is-iso-hom-Monoid : UU (l1 ⊔ l2)
  is-iso-hom-Monoid =
    is-iso-hom-Large-Precategory Monoid-Large-Precategory {X = M} {Y = N} f

  hom-inv-is-iso-hom-Monoid :
    is-iso-hom-Monoid → type-hom-Monoid N M
  hom-inv-is-iso-hom-Monoid =
    hom-inv-is-iso-hom-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      ( f)

  is-section-hom-inv-is-iso-hom-Monoid :
    (H : is-iso-hom-Monoid) →
    comp-hom-Monoid N M N f (hom-inv-is-iso-hom-Monoid H) ＝
    id-hom-Monoid N
  is-section-hom-inv-is-iso-hom-Monoid =
    is-section-hom-inv-is-iso-hom-Large-Precategory
      ( Monoid-Large-Precategory)
      { X = M}
      { Y = N}
      ( f)

  is-retraction-hom-inv-is-iso-hom-Monoid :
    (H : is-iso-hom-Monoid) →
    comp-hom-Monoid M N M (hom-inv-is-iso-hom-Monoid H) f ＝
    id-hom-Monoid M
  is-retraction-hom-inv-is-iso-hom-Monoid =
    is-retraction-hom-inv-is-iso-hom-Large-Precategory
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
    iso-Monoid → type-hom-Monoid M N
  hom-iso-Monoid =
    hom-iso-Large-Precategory Monoid-Large-Precategory M N

  is-iso-iso-Monoid :
    (f : iso-Monoid) →
    is-iso-hom-Monoid M N (hom-iso-Monoid f)
  is-iso-iso-Monoid =
    is-iso-iso-Large-Precategory Monoid-Large-Precategory M N

  hom-inv-iso-Monoid :
    iso-Monoid → type-hom-Monoid N M
  hom-inv-iso-Monoid =
    hom-inv-iso-Large-Precategory Monoid-Large-Precategory M N

  is-section-hom-inv-iso-Monoid :
    (f : iso-Monoid) →
    ( comp-hom-Monoid N M N
      ( hom-iso-Monoid f)
      ( hom-inv-iso-Monoid f)) ＝
    ( id-hom-Monoid N)
  is-section-hom-inv-iso-Monoid =
    is-section-hom-inv-iso-Large-Precategory Monoid-Large-Precategory M N

  is-retraction-hom-inv-iso-Monoid :
    (f : iso-Monoid) →
    ( comp-hom-Monoid M N M
      ( hom-inv-iso-Monoid f)
      ( hom-iso-Monoid f)) ＝
    ( id-hom-Monoid M)
  is-retraction-hom-inv-iso-Monoid =
    is-retraction-hom-inv-iso-Large-Precategory Monoid-Large-Precategory M N
```

## Examples

### Identity homomorphisms are isomorphisms

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-iso-id-hom-Monoid :
    is-iso-hom-Monoid M M (id-hom-Monoid M)
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

### Equalities give rise to isomorphisms

An equality between objects `x y : A` gives rise to an isomorphism between them.
This is because by the J-rule, it is enough to construct an isomorphism given
`refl : Id x x`, from `x` to itself. We take the identity morphism as such an
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

  is-prop-is-iso-hom-Monoid :
    (f : type-hom-Monoid M N) →
    is-prop (is-iso-hom-Monoid M N f)
  is-prop-is-iso-hom-Monoid =
    is-prop-is-iso-hom-Large-Precategory Monoid-Large-Precategory M N

  is-iso-prop-hom-Monoid :
    (f : type-hom-Monoid M N) → Prop (l1 ⊔ l2)
  is-iso-prop-hom-Monoid =
    is-iso-prop-hom-Large-Precategory Monoid-Large-Precategory M N
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
    is-set-iso-Large-Precategory Monoid-Large-Precategory M N

  iso-set-Monoid : Set (l1 ⊔ l2)
  iso-set-Monoid = iso-set-Large-Precategory Monoid-Large-Precategory M N
```

### Isomorphisms are stable by composition

```agda
module _
  {l1 l2 l3 : Level} (M : Monoid l1) (N : Monoid l2) (K : Monoid l3)
  (g : iso-Monoid N K) (f : iso-Monoid M N)
  where

  hom-comp-iso-Monoid : type-hom-Monoid M K
  hom-comp-iso-Monoid =
    hom-comp-iso-Large-Precategory Monoid-Large-Precategory M N K g f

  is-iso-comp-iso-Monoid :
    is-iso-hom-Monoid M K hom-comp-iso-Monoid
  is-iso-comp-iso-Monoid =
    is-iso-comp-iso-Large-Precategory Monoid-Large-Precategory M N K g f

  comp-iso-Monoid : iso-Monoid M K
  comp-iso-Monoid =
    comp-iso-Large-Precategory Monoid-Large-Precategory M N K g f
```

### Inverses of isomorphisms are isomorphisms

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2) (f : iso-Monoid M N)
  where

  is-iso-inv-iso-Monoid : is-iso-hom-Monoid N M (hom-inv-iso-Monoid M N f)
  is-iso-inv-iso-Monoid =
    is-iso-inv-iso-Large-Precategory Monoid-Large-Precategory M N f

  inv-iso-Monoid : iso-Monoid N M
  inv-iso-Monoid = inv-iso-Large-Precategory Monoid-Large-Precategory M N f
```
