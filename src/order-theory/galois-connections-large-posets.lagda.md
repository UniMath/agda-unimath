# Galois connections between large posets

```agda
module order-theory.galois-connections-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
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
`f : hom-Large-Poset (λ l → l) P Q` and `hom-Large-Poset id Q P` such that the
adjoint relation

```text
  (f x ≤ y) ↔ (x ≤ g y)
```

holds for every two elements `x : P` and `y : Q`.

The following table lists the Galois connections that have been formalized in
the agda-unimath library

{{#include tables/galois-connections.md}}

## Definitions

### The adjoint relation between order preserving maps between large posets

```agda
module _
  {αP αQ γ δ : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  (F : hom-Large-Poset γ P Q) (G : hom-Large-Poset δ Q P)
  where

  forward-implication-adjoint-relation-hom-Large-Poset : UUω
  forward-implication-adjoint-relation-hom-Large-Poset =
    {l1 l2 : Level}
    {x : type-Large-Poset P l1} {y : type-Large-Poset Q l2} →
    leq-Large-Poset Q (map-hom-Large-Poset P Q F x) y →
    leq-Large-Poset P x (map-hom-Large-Poset Q P G y)

  backward-implication-adjoint-relation-hom-Large-Poset : UUω
  backward-implication-adjoint-relation-hom-Large-Poset =
    {l1 l2 : Level}
    {x : type-Large-Poset P l1} {y : type-Large-Poset Q l2} →
    leq-Large-Poset P x (map-hom-Large-Poset Q P G y) →
    leq-Large-Poset Q (map-hom-Large-Poset P Q F x) y

  adjoint-relation-hom-Large-Poset : UUω
  adjoint-relation-hom-Large-Poset =
    {l1 l2 : Level}
    (x : type-Large-Poset P l1) (y : type-Large-Poset Q l2) →
    leq-Large-Poset Q (map-hom-Large-Poset P Q F x) y ↔
    leq-Large-Poset P x (map-hom-Large-Poset Q P G y)
```

### Galois connections between large posets

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
        hom-Large-Poset γ P Q
      upper-adjoint-galois-connection-Large-Poset :
        hom-Large-Poset δ Q P
      adjoint-relation-galois-connection-Large-Poset :
        adjoint-relation-hom-Large-Poset P Q
          lower-adjoint-galois-connection-Large-Poset
          upper-adjoint-galois-connection-Large-Poset

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

  forward-implication-adjoint-relation-galois-connection-Large-Poset :
    forward-implication-adjoint-relation-hom-Large-Poset P Q
      ( lower-adjoint-galois-connection-Large-Poset G)
      ( upper-adjoint-galois-connection-Large-Poset G)
  forward-implication-adjoint-relation-galois-connection-Large-Poset =
    forward-implication (adjoint-relation-galois-connection-Large-Poset G _ _)

  backward-implication-adjoint-relation-galois-connection-Large-Poset :
    backward-implication-adjoint-relation-hom-Large-Poset P Q
      ( lower-adjoint-galois-connection-Large-Poset G)
      ( upper-adjoint-galois-connection-Large-Poset G)
  backward-implication-adjoint-relation-galois-connection-Large-Poset =
    backward-implication (adjoint-relation-galois-connection-Large-Poset G _ _)
```

### Composition of Galois connections

```agda
module _
  {αP αQ αR : Level → Level} {βP βQ βR : Level → Level → Level}
  {γG γH : Level → Level} {δG δH : Level → Level}
  (P : Large-Poset αP βP)
  (Q : Large-Poset αQ βQ)
  (R : Large-Poset αR βR)
  (H : galois-connection-Large-Poset γH δH Q R)
  (G : galois-connection-Large-Poset γG δG P Q)
  where

  lower-adjoint-comp-galois-connection-Large-Poset :
    hom-Large-Poset (λ l → γH (γG l)) P R
  lower-adjoint-comp-galois-connection-Large-Poset =
    comp-hom-Large-Poset P Q R
      ( lower-adjoint-galois-connection-Large-Poset H)
      ( lower-adjoint-galois-connection-Large-Poset G)

  map-lower-adjoint-comp-galois-connection-Large-Poset :
    {l : Level} → type-Large-Poset P l → type-Large-Poset R (γH (γG l))
  map-lower-adjoint-comp-galois-connection-Large-Poset =
    map-comp-hom-Large-Poset P Q R
      ( lower-adjoint-galois-connection-Large-Poset H)
      ( lower-adjoint-galois-connection-Large-Poset G)

  preserves-order-lower-adjoint-comp-galois-connection-Large-Poset :
    preserves-order-map-Large-Poset P R
      map-lower-adjoint-comp-galois-connection-Large-Poset
  preserves-order-lower-adjoint-comp-galois-connection-Large-Poset =
    preserves-order-comp-hom-Large-Poset P Q R
      ( lower-adjoint-galois-connection-Large-Poset H)
      ( lower-adjoint-galois-connection-Large-Poset G)

  upper-adjoint-comp-galois-connection-Large-Poset :
    hom-Large-Poset (λ l → δG (δH l)) R P
  upper-adjoint-comp-galois-connection-Large-Poset =
    comp-hom-Large-Poset R Q P
      ( upper-adjoint-galois-connection-Large-Poset G)
      ( upper-adjoint-galois-connection-Large-Poset H)

  map-upper-adjoint-comp-galois-connection-Large-Poset :
    {l : Level} → type-Large-Poset R l → type-Large-Poset P (δG (δH l))
  map-upper-adjoint-comp-galois-connection-Large-Poset =
    map-comp-hom-Large-Poset R Q P
      ( upper-adjoint-galois-connection-Large-Poset G)
      ( upper-adjoint-galois-connection-Large-Poset H)

  preserves-order-upper-adjoint-comp-galois-connection-Large-Poset :
    preserves-order-map-Large-Poset R P
      map-upper-adjoint-comp-galois-connection-Large-Poset
  preserves-order-upper-adjoint-comp-galois-connection-Large-Poset =
    preserves-order-comp-hom-Large-Poset R Q P
      ( upper-adjoint-galois-connection-Large-Poset G)
      ( upper-adjoint-galois-connection-Large-Poset H)

  forward-implication-adjoint-relation-comp-galois-connection-Large-Poset :
    forward-implication-adjoint-relation-hom-Large-Poset P R
      lower-adjoint-comp-galois-connection-Large-Poset
      upper-adjoint-comp-galois-connection-Large-Poset
  forward-implication-adjoint-relation-comp-galois-connection-Large-Poset =
    forward-implication-adjoint-relation-galois-connection-Large-Poset P Q G ∘
    forward-implication-adjoint-relation-galois-connection-Large-Poset Q R H

  backward-implication-adjoint-relation-comp-galois-connection-Large-Poset :
    backward-implication-adjoint-relation-hom-Large-Poset P R
      lower-adjoint-comp-galois-connection-Large-Poset
      upper-adjoint-comp-galois-connection-Large-Poset
  backward-implication-adjoint-relation-comp-galois-connection-Large-Poset =
    backward-implication-adjoint-relation-galois-connection-Large-Poset Q R H ∘
    backward-implication-adjoint-relation-galois-connection-Large-Poset P Q G

  adjoint-relation-comp-galois-connection-Large-Poset :
    adjoint-relation-hom-Large-Poset P R
      lower-adjoint-comp-galois-connection-Large-Poset
      upper-adjoint-comp-galois-connection-Large-Poset
  pr1 (adjoint-relation-comp-galois-connection-Large-Poset x y) =
    forward-implication-adjoint-relation-comp-galois-connection-Large-Poset
  pr2 (adjoint-relation-comp-galois-connection-Large-Poset x y) =
    backward-implication-adjoint-relation-comp-galois-connection-Large-Poset

  comp-galois-connection-Large-Poset :
    galois-connection-Large-Poset (λ l → γH (γG l)) (λ l → δG (δH l)) P R
  lower-adjoint-galois-connection-Large-Poset
    comp-galois-connection-Large-Poset =
    lower-adjoint-comp-galois-connection-Large-Poset
  upper-adjoint-galois-connection-Large-Poset
    comp-galois-connection-Large-Poset =
    upper-adjoint-comp-galois-connection-Large-Poset
  adjoint-relation-galois-connection-Large-Poset
    comp-galois-connection-Large-Poset =
    adjoint-relation-comp-galois-connection-Large-Poset
```

### Homotopies of Galois connections

```agda
module _
  {αP αQ γ δ : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  (G H : galois-connection-Large-Poset γ δ P Q)
  where

  htpy-lower-adjoint-galois-connection-Large-Poset : UUω
  htpy-lower-adjoint-galois-connection-Large-Poset =
    htpy-hom-Large-Poset P Q
      ( lower-adjoint-galois-connection-Large-Poset G)
      ( lower-adjoint-galois-connection-Large-Poset H)

  htpy-upper-adjoint-galois-connection-Large-Poset : UUω
  htpy-upper-adjoint-galois-connection-Large-Poset =
    htpy-hom-Large-Poset Q P
      ( upper-adjoint-galois-connection-Large-Poset G)
      ( upper-adjoint-galois-connection-Large-Poset H)
```

## Properties

### A homotopy betwee lower adjoints of a galois connection induces a homotopy between upper adjoints, and vice versa

**Proof:** Consider two Galois connections `LG ⊣ UG` and `LH ⊣ UH` between `P`
and `Q`, and suppose that `LG(x) ＝ LH(x)` for all elements `x : P`. Then it
follows that

```text
  (x ≤ UG(y)) ↔ (LG(x) ≤ y) ↔ (LH(x) ≤ y) ↔ (x ≤ UH(y)).
```

Therefore it follows that `UG(y)` and `UH(y)` have the same lower sets, and
hence they must be equal.

```agda
module _
  {αP αQ γ δ : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  (G H : galois-connection-Large-Poset γ δ P Q)
  where

  htpy-upper-adjoint-htpy-lower-adjoint-galois-connection-Large-Poset :
    htpy-lower-adjoint-galois-connection-Large-Poset P Q G H →
    htpy-upper-adjoint-galois-connection-Large-Poset P Q G H
  htpy-upper-adjoint-htpy-lower-adjoint-galois-connection-Large-Poset = {!!}
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

    hom-f : hom-Large-Poset _ P Q
    hom-f = lower-adjoint-galois-connection-Large-Poset G

    f : {l : Level} → type-Large-Poset P l → type-Large-Poset Q (γ l)
    f = map-hom-Large-Poset P Q hom-f

    hom-g : hom-Large-Poset _ Q P
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
