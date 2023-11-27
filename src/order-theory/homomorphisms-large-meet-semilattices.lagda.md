# Homomorphisms of large meet-semilattices

```agda
module order-theory.homomorphisms-large-meet-semilattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.universe-levels

open import order-theory.large-meet-semilattices
open import order-theory.order-preserving-maps-large-posets
```

</details>

## Idea

An homomorphism of
[large meet-semilattices](order-theory.large-meet-semilattices.md) from `K` to
`L` is an
[order preserving map](order-theory.order-preserving-maps-large-posets.md) from
`K` to `L` which preserves meets and the top element.

## Definition

```agda
module _
  {αK αL : Level → Level} {βK βL : Level → Level → Level}
  (K : Large-Meet-Semilattice αK βK)
  (L : Large-Meet-Semilattice αL βL)
  where

  record
    hom-Large-Meet-Semilattice : UUω
    where
    field
      hom-large-poset-hom-Large-Meet-Semilattice :
        hom-Large-Poset
          ( λ l → l)
          ( large-poset-Large-Meet-Semilattice K)
          ( large-poset-Large-Meet-Semilattice L)
      preserves-meets-hom-Large-Meet-Semilattice :
        {l1 l2 : Level}
        (x : type-Large-Meet-Semilattice K l1)
        (y : type-Large-Meet-Semilattice K l2) →
        map-hom-Large-Poset
          ( large-poset-Large-Meet-Semilattice K)
          ( large-poset-Large-Meet-Semilattice L)
          ( hom-large-poset-hom-Large-Meet-Semilattice)
          ( meet-Large-Meet-Semilattice K x y) ＝
        meet-Large-Meet-Semilattice L
          ( map-hom-Large-Poset
            ( large-poset-Large-Meet-Semilattice K)
            ( large-poset-Large-Meet-Semilattice L)
            ( hom-large-poset-hom-Large-Meet-Semilattice)
            ( x))
          ( map-hom-Large-Poset
            ( large-poset-Large-Meet-Semilattice K)
            ( large-poset-Large-Meet-Semilattice L)
            ( hom-large-poset-hom-Large-Meet-Semilattice)
            ( y))
      preserves-top-hom-Large-Meet-Semilattice :
        map-hom-Large-Poset
          ( large-poset-Large-Meet-Semilattice K)
          ( large-poset-Large-Meet-Semilattice L)
          ( hom-large-poset-hom-Large-Meet-Semilattice)
          ( top-Large-Meet-Semilattice K) ＝
        top-Large-Meet-Semilattice L

  open hom-Large-Meet-Semilattice public

  module _
    (f : hom-Large-Meet-Semilattice)
    where

    map-hom-Large-Meet-Semilattice :
      {l1 : Level} →
      type-Large-Meet-Semilattice K l1 →
      type-Large-Meet-Semilattice L l1
    map-hom-Large-Meet-Semilattice =
      map-hom-Large-Poset
        ( large-poset-Large-Meet-Semilattice K)
        ( large-poset-Large-Meet-Semilattice L)
        ( hom-large-poset-hom-Large-Meet-Semilattice f)

    preserves-order-hom-Large-Meet-Semilattice :
      {l1 l2 : Level}
      (x : type-Large-Meet-Semilattice K l1)
      (y : type-Large-Meet-Semilattice K l2) →
      leq-Large-Meet-Semilattice K x y →
      leq-Large-Meet-Semilattice L
        ( map-hom-Large-Meet-Semilattice x)
        ( map-hom-Large-Meet-Semilattice y)
    preserves-order-hom-Large-Meet-Semilattice =
      preserves-order-hom-Large-Poset
        ( large-poset-Large-Meet-Semilattice K)
        ( large-poset-Large-Meet-Semilattice L)
        ( hom-large-poset-hom-Large-Meet-Semilattice f)
```
