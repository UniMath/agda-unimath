# Galois connections between large posets

```agda
module order-theory.galois-connections-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.functions
open import foundation.logical-equivalences
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.order-preserving-maps-large-posets
```

</details>

## Idea

A **galois connection** between [large posets](order-theory.large-posets.md) `P`
and `Q` consists of
[order preserving maps](order-theory.order-preserving-maps-large-posets.md)
`f : hom-Large-Poset id P Q` and `hom-Large-Poset id Q P` such that the adjoint
relation

```md
  (f x ≤ y) ↔ (x ≤ g y)
```

holds for every two elements `x : P` and `y : Q`.

## Definition

```agda
module _
  {αP αQ : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  where

  record
    galois-connection-Large-Poset : UUω
    where
    field
      lower-adjoint-galois-connection-Large-Poset :
        hom-Large-Poset id P Q
      upper-adjoint-galois-connection-Large-Poset :
        hom-Large-Poset id Q P
      adjoint-relation-galois-connection-Large-Poset :
        {l1 l2 : Level}
        (x : type-Large-Poset P l1) (y : type-Large-Poset Q l2) →
        leq-Large-Poset Q
          ( map-hom-Large-Poset P Q
            ( lower-adjoint-galois-connection-Large-Poset)
            ( x))
          ( y) ↔
        leq-Large-Poset P x
          ( map-hom-Large-Poset Q P
            ( upper-adjoint-galois-connection-Large-Poset)
            ( y))

  open galois-connection-Large-Poset public

  module _
    (G : galois-connection-Large-Poset)
    where

    map-lower-adjoint-galois-connection-Large-Poset :
      {l1 : Level} → type-Large-Poset P l1 → type-Large-Poset Q l1
    map-lower-adjoint-galois-connection-Large-Poset =
      map-hom-Large-Poset P Q
        ( lower-adjoint-galois-connection-Large-Poset G)

    preserves-order-lower-adjoint-galois-connection-Large-Poset :
      {l1 l2 : Level} (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
      leq-Large-Poset P x y →
      leq-Large-Poset Q
        ( map-lower-adjoint-galois-connection-Large-Poset x)
        ( map-lower-adjoint-galois-connection-Large-Poset y)
    preserves-order-lower-adjoint-galois-connection-Large-Poset =
      preserves-order-hom-Large-Poset P Q
        ( lower-adjoint-galois-connection-Large-Poset G)

    map-upper-adjoint-galois-connection-Large-Poset :
      {l1 : Level} → type-Large-Poset Q l1 → type-Large-Poset P l1
    map-upper-adjoint-galois-connection-Large-Poset =
      map-hom-Large-Poset Q P
        ( upper-adjoint-galois-connection-Large-Poset G)

    preserves-order-upper-adjoint-galois-connection-Large-Poset :
      {l1 l2 : Level} (x : type-Large-Poset Q l1) (y : type-Large-Poset Q l2) →
      leq-Large-Poset Q x y →
      leq-Large-Poset P
        ( map-upper-adjoint-galois-connection-Large-Poset x)
        ( map-upper-adjoint-galois-connection-Large-Poset y)
    preserves-order-upper-adjoint-galois-connection-Large-Poset =
      preserves-order-hom-Large-Poset Q P
        ( upper-adjoint-galois-connection-Large-Poset G)
```
