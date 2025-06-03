# Homomorphisms of large suplattices

```agda
module order-theory.homomorphisms-large-suplattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.universe-levels

open import order-theory.large-suplattices
open import order-theory.order-preserving-maps-large-posets
```

</details>

## Idea

A **homomorphism of large suplattices** is an
[order preserving map](order-theory.order-preserving-maps-large-posets.md) that
preserves least upper bounds.

## Definitions

### The predicate of being a homomorphism of large suplattices

```agda
module _
  {αK αL : Level → Level} {βK βL : Level → Level → Level}
  {γ : Level}
  (K : Large-Suplattice αK βK γ) (L : Large-Suplattice αL βL γ)
  where

  preserves-sup-hom-Large-Poset :
    hom-Large-Poset
      ( λ l → l)
      ( large-poset-Large-Suplattice K)
      ( large-poset-Large-Suplattice L) →
    UUω
  preserves-sup-hom-Large-Poset f =
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Suplattice K l2) →
    ( map-hom-Large-Poset
      ( large-poset-Large-Suplattice K)
      ( large-poset-Large-Suplattice L)
      ( f)
      ( sup-Large-Suplattice K x)) ＝
    sup-Large-Suplattice L
      ( λ i →
        map-hom-Large-Poset
          ( large-poset-Large-Suplattice K)
          ( large-poset-Large-Suplattice L)
          ( f)
          ( x i))

  record
    hom-Large-Suplattice : UUω
    where
    field
      hom-large-poset-hom-Large-Suplattice :
        hom-Large-Poset
          ( λ l → l)
          ( large-poset-Large-Suplattice K)
          ( large-poset-Large-Suplattice L)
      preserves-sup-hom-Large-Suplattice :
        preserves-sup-hom-Large-Poset hom-large-poset-hom-Large-Suplattice

  open hom-Large-Suplattice public

  module _
    (f : hom-Large-Suplattice)
    where

    map-hom-Large-Suplattice :
      {l1 : Level} →
      type-Large-Suplattice K l1 → type-Large-Suplattice L l1
    map-hom-Large-Suplattice =
      map-hom-Large-Poset
        ( large-poset-Large-Suplattice K)
        ( large-poset-Large-Suplattice L)
        ( hom-large-poset-hom-Large-Suplattice f)

    preserves-order-hom-Large-Suplattice :
      {l1 l2 : Level}
      (x : type-Large-Suplattice K l1) (y : type-Large-Suplattice K l2) →
      leq-Large-Suplattice K x y →
      leq-Large-Suplattice L
        ( map-hom-Large-Suplattice x)
        ( map-hom-Large-Suplattice y)
    preserves-order-hom-Large-Suplattice =
      preserves-order-hom-Large-Poset
        ( large-poset-Large-Suplattice K)
        ( large-poset-Large-Suplattice L)
        ( hom-large-poset-hom-Large-Suplattice f)
```
