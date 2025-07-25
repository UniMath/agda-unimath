# Pullbacks of subsemigroups

```agda
module group-theory.pullbacks-subsemigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.powersets
open import foundation.pullbacks-subtypes
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups
open import group-theory.semigroups
open import group-theory.subsemigroups
open import group-theory.subsets-semigroups

open import order-theory.commuting-squares-of-order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.similarity-of-order-preserving-maps-large-posets
```

</details>

## Idea

Given a [semigroup homomorphism](group-theory.homomorphisms-semigroups.md)
`f : G → H` into a [semigroup](group-theory.semigroups.md) `H` equipped with a
[subsemigroup](group-theory.subsemigroups.md) `K ≤ H`, the **pullback**
`pullback f K` of `K` along `f` is defined by substituting `f` in `K`. In other
words, it is the subsemigroup `pullback f K` of `G` consisting of the elements
`x : G` such that `f x ∈ K`.

## Definitions

### The pullback of a subsemigroup along a semigroup homomorphism

```agda
module _
  {l1 l2 l3 : Level} (G : Semigroup l1) (H : Semigroup l2)
  (f : hom-Semigroup G H) (K : Subsemigroup l3 H)
  where

  subset-pullback-Subsemigroup : subset-Semigroup l3 G
  subset-pullback-Subsemigroup =
    subset-Subsemigroup H K ∘ map-hom-Semigroup G H f

  is-closed-under-multiplication-pullback-Subsemigroup :
    is-closed-under-multiplication-subset-Semigroup G
      subset-pullback-Subsemigroup
  is-closed-under-multiplication-pullback-Subsemigroup p q =
    is-closed-under-eq-Subsemigroup' H K
      ( is-closed-under-multiplication-Subsemigroup H K p q)
      ( preserves-mul-hom-Semigroup G H f)

  pullback-Subsemigroup : Subsemigroup l3 G
  pr1 pullback-Subsemigroup =
    subset-pullback-Subsemigroup
  pr2 pullback-Subsemigroup =
    is-closed-under-multiplication-pullback-Subsemigroup

  is-in-pullback-Subsemigroup : type-Semigroup G → UU l3
  is-in-pullback-Subsemigroup =
    is-in-Subsemigroup G pullback-Subsemigroup

  is-closed-under-eq-pullback-Subsemigroup :
    {x y : type-Semigroup G} →
    is-in-pullback-Subsemigroup x → x ＝ y → is-in-pullback-Subsemigroup y
  is-closed-under-eq-pullback-Subsemigroup =
    is-closed-under-eq-Subsemigroup G pullback-Subsemigroup

  is-closed-under-eq-pullback-Subsemigroup' :
    {x y : type-Semigroup G} →
    is-in-pullback-Subsemigroup y → x ＝ y → is-in-pullback-Subsemigroup x
  is-closed-under-eq-pullback-Subsemigroup' =
    is-closed-under-eq-Subsemigroup' G pullback-Subsemigroup
```

### The order preserving operation `pullback-Subsemigroup`

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2) (f : hom-Semigroup G H)
  where

  preserves-order-pullback-Subsemigroup :
    {l3 l4 : Level} (S : Subsemigroup l3 H) (T : Subsemigroup l4 H) →
    leq-Subsemigroup H S T →
    leq-Subsemigroup G
      ( pullback-Subsemigroup G H f S)
      ( pullback-Subsemigroup G H f T)
  preserves-order-pullback-Subsemigroup S T =
    preserves-order-pullback-subtype
      ( map-hom-Semigroup G H f)
      ( subset-Subsemigroup H S)
      ( subset-Subsemigroup H T)

  pullback-hom-large-poset-Subsemigroup :
    hom-Large-Poset
      ( λ l → l)
      ( Subsemigroup-Large-Poset H)
      ( Subsemigroup-Large-Poset G)
  map-hom-Large-Preorder pullback-hom-large-poset-Subsemigroup =
    pullback-Subsemigroup G H f
  preserves-order-hom-Large-Preorder pullback-hom-large-poset-Subsemigroup =
    preserves-order-pullback-Subsemigroup
```

## Properties

### The pullback operation commutes with the underlying subtype operation

The square

```text
                       pullback f
    Subsemigroup H ----------------> Subsemigroup G
          |                                |
   K ↦ UK |                                | K ↦ UK
          |                                |
          ∨                                ∨
  subset-Semigroup H ------------> subset-Semigroup G
                      pullback f
```

of [order preserving maps](order-theory.order-preserving-maps-large-posets.md)
[commutes](order-theory.commuting-squares-of-order-preserving-maps-large-posets.md)
by reflexivity.

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2) (f : hom-Semigroup G H)
  where

  coherence-square-pullback-subset-Subsemigroup :
    coherence-square-hom-Large-Poset
      ( Subsemigroup-Large-Poset H)
      ( powerset-Large-Poset (type-Semigroup H))
      ( Subsemigroup-Large-Poset G)
      ( powerset-Large-Poset (type-Semigroup G))
      ( pullback-hom-large-poset-Subsemigroup G H f)
      ( subset-subsemigroup-hom-large-poset-Semigroup H)
      ( subset-subsemigroup-hom-large-poset-Semigroup G)
      ( pullback-subtype-hom-Large-Poset (map-hom-Semigroup G H f))
  coherence-square-pullback-subset-Subsemigroup =
    refl-sim-hom-Large-Poset
      ( Subsemigroup-Large-Poset H)
      ( powerset-Large-Poset (type-Semigroup G))
      ( comp-hom-Large-Poset
        ( Subsemigroup-Large-Poset H)
        ( Subsemigroup-Large-Poset G)
        ( powerset-Large-Poset (type-Semigroup G))
        ( subset-subsemigroup-hom-large-poset-Semigroup G)
        ( pullback-hom-large-poset-Subsemigroup G H f))
```
