# Homomorphisms of large frames

```agda
module order-theory.homomorphisms-large-frames where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.universe-levels

open import order-theory.homomorphisms-large-meet-semilattices
open import order-theory.homomorphisms-large-suplattices
open import order-theory.large-frames
```

</details>

## Idea

A **homomorphism of large frames** from `K` to `L` is an order preserving map
from `K` to `L` which preserves meets, the top element, and suprema.

## Definitions

### Homomorphisms of frames

```agda
module _
  {αK αL : Level → Level} {βK βL : Level → Level → Level} {γ : Level}
  (K : Large-Frame αK βK γ) (L : Large-Frame αL βL γ)
  where

  record
    hom-Large-Frame : UUω
    where
    field
      hom-large-meet-semilattice-hom-Large-Frame :
        hom-Large-Meet-Semilattice
          ( large-meet-semilattice-Large-Frame K)
          ( large-meet-semilattice-Large-Frame L)
      preserves-sup-hom-Large-Frame :
        preserves-sup-hom-Large-Poset
          ( large-suplattice-Large-Frame K)
          ( large-suplattice-Large-Frame L)
          ( hom-large-poset-hom-Large-Meet-Semilattice
            ( hom-large-meet-semilattice-hom-Large-Frame))

  open hom-Large-Frame public

  module _
    (f : hom-Large-Frame)
    where

    map-hom-Large-Frame :
      {l1 : Level} → type-Large-Frame K l1 → type-Large-Frame L l1
    map-hom-Large-Frame =
      map-hom-Large-Meet-Semilattice
        ( large-meet-semilattice-Large-Frame K)
        ( large-meet-semilattice-Large-Frame L)
        ( hom-large-meet-semilattice-hom-Large-Frame f)

    preserves-order-hom-Large-Frame :
      {l1 l2 : Level} (x : type-Large-Frame K l1) (y : type-Large-Frame K l2) →
      leq-Large-Frame K x y →
      leq-Large-Frame L (map-hom-Large-Frame x) (map-hom-Large-Frame y)
    preserves-order-hom-Large-Frame =
      preserves-order-hom-Large-Meet-Semilattice
        ( large-meet-semilattice-Large-Frame K)
        ( large-meet-semilattice-Large-Frame L)
        ( hom-large-meet-semilattice-hom-Large-Frame f)

    preserves-meets-hom-Large-Frame :
      {l1 l2 : Level} (x : type-Large-Frame K l1) (y : type-Large-Frame K l2) →
      map-hom-Large-Frame (meet-Large-Frame K x y) ＝
      meet-Large-Frame L (map-hom-Large-Frame x) (map-hom-Large-Frame y)
    preserves-meets-hom-Large-Frame =
      preserves-meets-hom-Large-Meet-Semilattice
        ( hom-large-meet-semilattice-hom-Large-Frame f)

    preserves-top-hom-Large-Frame :
      map-hom-Large-Frame (top-Large-Frame K) ＝ top-Large-Frame L
    preserves-top-hom-Large-Frame =
      preserves-top-hom-Large-Meet-Semilattice
        ( hom-large-meet-semilattice-hom-Large-Frame f)
```
