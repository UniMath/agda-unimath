# Galois connections between large posets

```agda
module order-theory.galois-connections-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.logical-equivalences
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.least-upper-bounds-large-posets
open import order-theory.order-preserving-maps-large-posets
open import order-theory.principal-lower-sets-large-posets
open import order-theory.principal-upper-sets-large-posets
open import order-theory.similarity-of-elements-large-posets
open import order-theory.similarity-of-order-preserving-maps-large-posets
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

**Homotopies of Galois connections** are pointwise identifications between
either their lower adjoints or their upper adjoints. We will show below that
homotopies between lower adjoints induce homotopies between upper adjoints and
vice versa.

**Note:** We can only have homotopies between Galois connections with the same
universe level reindexing functions.

```agda
module _
  {αP αQ γ δ : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  (G H : galois-connection-Large-Poset γ δ P Q)
  where

  lower-htpy-galois-connection-Large-Poset : UUω
  lower-htpy-galois-connection-Large-Poset =
    htpy-hom-Large-Poset P Q
      ( lower-adjoint-galois-connection-Large-Poset G)
      ( lower-adjoint-galois-connection-Large-Poset H)

  upper-htpy-galois-connection-Large-Poset : UUω
  upper-htpy-galois-connection-Large-Poset =
    htpy-hom-Large-Poset Q P
      ( upper-adjoint-galois-connection-Large-Poset G)
      ( upper-adjoint-galois-connection-Large-Poset H)
```

### Similarity of Galois connections

**Similarities of Galois connections** are pointwise
[similarities](order-theory.similarity-of-elements-large-posets.md) between
either their lower or their upper adjoints. We will show below that similarities
between lower adjoints induce similarities between upper adjoints and vice
versa.

**Note:** Since the notion of similarity applies to galois connections with not
necessarily the same universe level reindexing function, it is slightly more
flexible. For this reason, it may be easier to work with similarity of galois
connections.

```agda
module _
  {αP αQ γG γH δG δH : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  (G : galois-connection-Large-Poset γG δG P Q)
  (H : galois-connection-Large-Poset γH δH P Q)
  where

  sim-lower-galois-connection-Large-Poset : UUω
  sim-lower-galois-connection-Large-Poset =
    sim-hom-Large-Poset P Q
      ( lower-adjoint-galois-connection-Large-Poset G)
      ( lower-adjoint-galois-connection-Large-Poset H)

  sim-upper-galois-connection-Large-Poset : UUω
  sim-upper-galois-connection-Large-Poset =
    sim-hom-Large-Poset Q P
      ( upper-adjoint-galois-connection-Large-Poset G)
      ( upper-adjoint-galois-connection-Large-Poset H)
```

### Lower universal objects of galois connections

Consider a Galois connection `G : P → Q` and an element `x : P`. An element
`x' : Q` is then said to satisfy the **lower universal property** with respect
to `x` if the logical equivalence

```text
  (x' ≤-Q y) ↔ (x ≤-P UG y)
```

holds for every element `y : Q`.

```agda
module _
  {αP αQ γ δ : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  (G : galois-connection-Large-Poset γ δ P Q)
  {l1 l2 : Level} (x : type-Large-Poset P l1)
  (x' : type-Large-Poset Q l2)
  where

  is-lower-element-galois-connection-Large-Poset : UUω
  is-lower-element-galois-connection-Large-Poset =
    {l : Level} (y : type-Large-Poset Q l) →
    leq-Large-Poset Q x' y ↔
    leq-Large-Poset P x
      ( map-upper-adjoint-galois-connection-Large-Poset P Q G y)
```

### Upper universal objects of galois connections

Consider a Galois connection `G : P → Q` and an element `y : Q`. An element
`y' : P` is then said to satisfy the **upper universal property** with respect
to `y` if the logical equivalence

```text
  (LG x ≤-Q y) ↔ (x ≤-P y')
```

holds for every element `x : P`.

```agda
module _
  {αP αQ γ δ : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  (G : galois-connection-Large-Poset γ δ P Q)
  {l1 l2 : Level} (y : type-Large-Poset Q l1)
  (y' : type-Large-Poset P l2)
  where

  is-upper-element-galois-connection-Large-Poset : UUω
  is-upper-element-galois-connection-Large-Poset =
    {l : Level} (x : type-Large-Poset P l) →
    leq-Large-Poset Q
      ( map-lower-adjoint-galois-connection-Large-Poset P Q G x)
      ( y) ↔
    leq-Large-Poset P x y'
```

## Properties

### A similarity between lower adjoints of a Galois connection induces a similarity between upper adjoints, and vice versa

**Proof:** Consider two Galois connections `LG ⊣ UG` and `LH ⊣ UH` between `P`
and `Q`, and suppose that `LG(x) ~ LH(x)` for all elements `x : P`. Then it
follows that

```text
  (x ≤ UG(y)) ↔ (LG(x) ≤ y) ↔ (LH(x) ≤ y) ↔ (x ≤ UH(y)).
```

Therefore it follows that `UG(y)` and `UH(y)` have the same lower sets, and
hence they must be equal.

```agda
module _
  {αP αQ γG γH δG δH : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  (G : galois-connection-Large-Poset γG δG P Q)
  (H : galois-connection-Large-Poset γH δH P Q)
  where

  sim-upper-sim-lower-galois-connection-Large-Poset :
    sim-lower-galois-connection-Large-Poset P Q G H →
    sim-upper-galois-connection-Large-Poset P Q H G
  sim-upper-sim-lower-galois-connection-Large-Poset
    p x =
    sim-has-same-elements-principal-lower-set-element-Large-Poset P
      ( λ y →
        logical-equivalence-reasoning
          leq-Large-Poset P y
            ( map-upper-adjoint-galois-connection-Large-Poset P Q H x)
          ↔ leq-Large-Poset Q
              ( map-lower-adjoint-galois-connection-Large-Poset P Q H y)
              ( x)
            by inv-iff (adjoint-relation-galois-connection-Large-Poset H y x)
          ↔ leq-Large-Poset Q
              ( map-lower-adjoint-galois-connection-Large-Poset P Q G y)
              ( x)
            by
            inv-iff
              ( has-same-elements-principal-upper-set-element-sim-Large-Poset Q
                ( p y)
                ( x))
          ↔ leq-Large-Poset P y
              ( map-upper-adjoint-galois-connection-Large-Poset P Q G x)
            by adjoint-relation-galois-connection-Large-Poset G y x)

  sim-lower-sim-upper-galois-connection-Large-Poset :
    sim-upper-galois-connection-Large-Poset P Q H G →
    sim-lower-galois-connection-Large-Poset P Q G H
  sim-lower-sim-upper-galois-connection-Large-Poset
    p y =
    sim-has-same-elements-principal-upper-set-element-Large-Poset Q
      ( λ x →
        logical-equivalence-reasoning
          leq-Large-Poset Q
            ( map-lower-adjoint-galois-connection-Large-Poset P Q G y)
            ( x)
          ↔ leq-Large-Poset P y
              ( map-upper-adjoint-galois-connection-Large-Poset P Q G x)
            by adjoint-relation-galois-connection-Large-Poset G y x
          ↔ leq-Large-Poset P y
              ( map-upper-adjoint-galois-connection-Large-Poset P Q H x)
            by
            inv-iff
              ( has-same-elements-principal-lower-set-element-sim-Large-Poset P
                ( p x)
                ( y))
          ↔ leq-Large-Poset Q
              ( map-lower-adjoint-galois-connection-Large-Poset P Q H y)
              ( x)
            by inv-iff (adjoint-relation-galois-connection-Large-Poset H y x))
```

### A homotopy between lower adjoints of a Galois connection induces a homotopy between upper adjoints, and vice versa

**Proof:** Consider two Galois connections `LG ⊣ UG` and `LH ⊣ UH` between `P`
and `Q`, and suppose that `LG ~ LH`. Then there is a similarity `LG ≈ LH`, and
this induces a similarity `UG ≈ UH`. In other words, we obtain that

```text
  UG y ~ UH y
```

for any element `y : Q`. Since `UG y` and `UH y` are of the same universe level,
it follows that they are equal.

```agda
module _
  {αP αQ γ δ : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  (G H : galois-connection-Large-Poset γ δ P Q)
  where

  upper-htpy-lower-htpy-galois-connection-Large-Poset :
    lower-htpy-galois-connection-Large-Poset P Q G H →
    upper-htpy-galois-connection-Large-Poset P Q G H
  upper-htpy-lower-htpy-galois-connection-Large-Poset p =
    htpy-sim-hom-Large-Poset Q P
      ( upper-adjoint-galois-connection-Large-Poset G)
      ( upper-adjoint-galois-connection-Large-Poset H)
      ( sim-upper-sim-lower-galois-connection-Large-Poset P Q H G
        ( sim-htpy-hom-Large-Poset P Q
          ( lower-adjoint-galois-connection-Large-Poset H)
          ( lower-adjoint-galois-connection-Large-Poset G)
          ( inv-htpy p)))

  lower-htpy-upper-htpy-galois-connection-Large-Poset :
    upper-htpy-galois-connection-Large-Poset P Q H G →
    lower-htpy-galois-connection-Large-Poset P Q G H
  lower-htpy-upper-htpy-galois-connection-Large-Poset p =
    htpy-sim-hom-Large-Poset P Q
      ( lower-adjoint-galois-connection-Large-Poset G)
      ( lower-adjoint-galois-connection-Large-Poset H)
      ( sim-lower-sim-upper-galois-connection-Large-Poset P Q G H
        ( sim-htpy-hom-Large-Poset Q P
          ( upper-adjoint-galois-connection-Large-Poset H)
          ( upper-adjoint-galois-connection-Large-Poset G)
          ( p)))
```

### An element `x' : Q` satisfies the lower universal property with respect to `x : P` if and only if it is similar to the element `LG x`

```agda
module _
  {αP αQ : Level → Level} {βP βQ : Level → Level → Level}
  {γ δ : Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  (G : galois-connection-Large-Poset γ δ P Q)
  {l1 l2 : Level} (x : type-Large-Poset P l1) (x' : type-Large-Poset Q l2)
  where

  is-lower-element-sim-galois-connection-Large-Poset :
    sim-Large-Poset Q
      ( map-lower-adjoint-galois-connection-Large-Poset P Q G x)
      ( x') →
    is-lower-element-galois-connection-Large-Poset P Q G x x'
  pr1 (is-lower-element-sim-galois-connection-Large-Poset s y) p =
    forward-implication-adjoint-relation-galois-connection-Large-Poset P Q G
      ( transitive-leq-Large-Poset Q _ x' y p (pr1 s))
  pr2 (is-lower-element-sim-galois-connection-Large-Poset s y) p =
    transitive-leq-Large-Poset Q x' _ y
      ( backward-implication-adjoint-relation-galois-connection-Large-Poset
        P Q G p)
      ( pr2 s)

  sim-is-lower-element-galois-connection-Large-Poset :
    is-lower-element-galois-connection-Large-Poset P Q G x x' →
    sim-Large-Poset Q
      ( map-lower-adjoint-galois-connection-Large-Poset P Q G x)
      ( x')
  sim-is-lower-element-galois-connection-Large-Poset l =
    sim-has-same-elements-principal-upper-set-element-Large-Poset Q
      ( λ y →
        logical-equivalence-reasoning
          leq-Large-Poset Q _ y
          ↔ leq-Large-Poset P x _
            by adjoint-relation-galois-connection-Large-Poset G x y
          ↔ leq-Large-Poset Q x' y
            by inv-iff (l y))
```

### An element `y' : P` satisfies the upper universal property with respect to `y : Q` if and only if it is similar to the element `UG y`

```agda
module _
  {αP αQ : Level → Level} {βP βQ : Level → Level → Level}
  {γ δ : Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  (G : galois-connection-Large-Poset γ δ P Q)
  {l1 l2 : Level} (y : type-Large-Poset Q l1) (y' : type-Large-Poset P l2)
  where

  is-upper-element-sim-galois-connection-Large-Poset :
    sim-Large-Poset P
      ( map-upper-adjoint-galois-connection-Large-Poset P Q G y)
      ( y') →
    is-upper-element-galois-connection-Large-Poset P Q G y y'
  pr1 (is-upper-element-sim-galois-connection-Large-Poset s x) p =
    transitive-leq-Large-Poset P x _ y'
      ( pr1 s)
      ( forward-implication-adjoint-relation-galois-connection-Large-Poset
        P Q G p)
  pr2 (is-upper-element-sim-galois-connection-Large-Poset s x) p =
    backward-implication-adjoint-relation-galois-connection-Large-Poset P Q G
      ( transitive-leq-Large-Poset P x y' _ (pr2 s) p)

  sim-is-upper-element-galois-connection-Large-Poset :
    is-upper-element-galois-connection-Large-Poset P Q G y y' →
    sim-Large-Poset P
      ( map-upper-adjoint-galois-connection-Large-Poset P Q G y)
      ( y')
  sim-is-upper-element-galois-connection-Large-Poset u =
    sim-has-same-elements-principal-lower-set-element-Large-Poset P
      ( λ x →
        logical-equivalence-reasoning
          leq-Large-Poset P x _
          ↔ leq-Large-Poset Q _ y
            by inv-iff (adjoint-relation-galois-connection-Large-Poset G x y)
          ↔ leq-Large-Poset P x y'
            by u x)
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
