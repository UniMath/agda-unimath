# Galois connections between large posets

```agda
module order-theory.galois-connections-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.logical-equivalences
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.least-upper-bounds-large-posets
open import order-theory.order-preserving-maps-large-posets
```

</details>

## Idea

A **galois connection** between [large posets](order-theory.large-posets.md) `P`
and `Q` consists of
[order preserving maps](order-theory.order-preserving-maps-large-posets.md)
`f : hom-set-Large-Poset id P Q` and `hom-set-Large-Poset id Q P` such that the
adjoint relation

```text
  (f x ≤ y) ↔ (x ≤ g y)
```

holds for every two elements `x : P` and `y : Q`.

The following table lists the Galois connections that have been formalized in
the agda-unimath library

{{#include tables/galois-connections.md}}

## Definition

```agda
module _
  {αP αQ : Level → Level} {βP βQ : Level → Level → Level}
  (γ : Level → Level) (δ : Level → Level)
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  where

  record
    galois-connection-Large-Poset : UUω
    where
    constructor
      make-galois-connection-Large-Poset
    field
      lower-adjoint-galois-connection-Large-Poset :
        hom-set-Large-Poset γ P Q
      upper-adjoint-galois-connection-Large-Poset :
        hom-set-Large-Poset δ Q P
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
  {αP αQ : Level → Level} {βP βQ : Level → Level → Level}
  {γ : Level → Level} {δ : Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  (G : galois-connection-Large-Poset γ δ P Q)
  where

  map-lower-adjoint-galois-connection-Large-Poset :
    {l1 : Level} → type-Large-Poset P l1 → type-Large-Poset Q (γ l1)
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
    {l1 : Level} → type-Large-Poset Q l1 → type-Large-Poset P (δ l1)
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

### The lower adjoint of a Galois connection preserves all existing joins

```agda
module _
  {αP αQ : Level → Level} {βP βQ : Level → Level → Level}
  {γ δ : Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  (G : galois-connection-Large-Poset γ δ P Q)
  where

  private
    _≤-P_ :
      {l1 l2 : Level} → type-Large-Poset P l1 → type-Large-Poset P l2 →
      UU (βP l1 l2)
    _≤-P_ = leq-Large-Poset P

    _≤-Q_ :
      {l1 l2 : Level} → type-Large-Poset Q l1 → type-Large-Poset Q l2 →
      UU (βQ l1 l2)
    _≤-Q_ = leq-Large-Poset Q

    hom-f : hom-set-Large-Poset _ P Q
    hom-f = lower-adjoint-galois-connection-Large-Poset G

    f : {l : Level} → type-Large-Poset P l → type-Large-Poset Q (γ l)
    f = map-hom-Large-Poset P Q hom-f

    hom-g : hom-set-Large-Poset _ Q P
    hom-g = upper-adjoint-galois-connection-Large-Poset G

    g : {l : Level} → type-Large-Poset Q l → type-Large-Poset P (δ l)
    g = map-hom-Large-Poset Q P hom-g

    adjoint-relation-G :
      {l1 l2 : Level}
      (x : type-Large-Poset P l1) (y : type-Large-Poset Q l2) →
      leq-Large-Poset Q (f x) y ↔
      leq-Large-Poset P x (g y)
    adjoint-relation-G = adjoint-relation-galois-connection-Large-Poset G

  preserves-join-lower-adjoint-galois-connection-Large-Poset :
    {l1 l2 l3 : Level} {U : UU l1} (x : U → type-Large-Poset P l2)
    (y : type-Large-Poset P l3) →
    is-least-upper-bound-family-of-elements-Large-Poset P x y →
    is-least-upper-bound-family-of-elements-Large-Poset Q
      ( λ α → f (x α))
      ( f y)
  preserves-join-lower-adjoint-galois-connection-Large-Poset x y H z =
    logical-equivalence-reasoning
      ((α : _) → f (x α) ≤-Q z)
      ↔ ((α : _) → (x α) ≤-P g z)
        by iff-Π-iff-family (λ α → adjoint-relation-G (x α) z)
      ↔ y ≤-P g z by H (g z)
      ↔ f y ≤-Q z by inv-iff (adjoint-relation-G y z)
```
