# Order preserving maps between large posets

```agda
module order-theory.order-preserving-maps-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies

open import order-theory.large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.similarity-of-elements-large-posets
```

</details>

## Idea

An **order preserving map** between [large posets](order-theory.large-posets.md)
`P` and `Q` consists of a map

```text
  f : type-Large-Poset P l1 → type-Large-Poset Q (γ l1)
```

for each [universe level](foundation.universe-levels.md) `l1`, such that `x ≤ y`
implies `f x ≤ f y` for any two elements `x y : P`. The function
`γ : Level → Level` that specifies the universe level of `f x` in terms of the
universe level of `x` is called the **universe level reindexing function** of
the order preserving map `f`.

## Definitions

### The predicate that a map between large posets is order preserving

```agda
module _
  {αP αQ : Level → Level} {βP βQ : Level → Level → Level} {γ : Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  where

  preserves-order-map-Large-Poset :
    ({l : Level} → type-Large-Poset P l → type-Large-Poset Q (γ l)) →
    UUω
  preserves-order-map-Large-Poset =
    preserves-order-map-Large-Preorder
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)
```

### The type of order preserving maps between large posets

```agda
module _
  {αP αQ : Level → Level} {βP βQ : Level → Level → Level}
  (γ : Level → Level)
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  where

  hom-Large-Poset : UUω
  hom-Large-Poset =
    hom-Large-Preorder γ
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)

module _
  {αP αQ γ : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ) (f : hom-Large-Poset γ P Q)
  where

  map-hom-Large-Poset :
    {l : Level} → type-Large-Poset P l → type-Large-Poset Q (γ l)
  map-hom-Large-Poset =
    map-hom-Large-Preorder f

  preserves-order-hom-Large-Poset :
    preserves-order-map-Large-Poset P Q map-hom-Large-Poset
  preserves-order-hom-Large-Poset =
    preserves-order-hom-Large-Preorder f
```

### The identity order preserving map on a large poset

```agda
module _
  {αP : Level → Level} {βP : Level → Level → Level} (P : Large-Poset αP βP)
  where

  id-hom-Large-Poset : hom-Large-Poset (λ l → l) P P
  id-hom-Large-Poset = id-hom-Large-Preorder (large-preorder-Large-Poset P)
```

### Composition of order preserving maps between large posets

```agda
module _
  {αP αQ αR γg γf : Level → Level} {βP βQ βR : Level → Level → Level}
  (P : Large-Poset αP βP)
  (Q : Large-Poset αQ βQ)
  (R : Large-Poset αR βR)
  (g : hom-Large-Poset γg Q R)
  (f : hom-Large-Poset γf P Q)
  where

  map-comp-hom-Large-Poset :
    {l1 : Level} → type-Large-Poset P l1 → type-Large-Poset R (γg (γf l1))
  map-comp-hom-Large-Poset =
    map-comp-hom-Large-Preorder
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)
      ( large-preorder-Large-Poset R)
      ( g)
      ( f)

  preserves-order-comp-hom-Large-Poset :
    preserves-order-map-Large-Poset P R map-comp-hom-Large-Poset
  preserves-order-comp-hom-Large-Poset =
    preserves-order-comp-hom-Large-Preorder
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)
      ( large-preorder-Large-Poset R)
      ( g)
      ( f)

  comp-hom-Large-Poset : hom-Large-Poset (λ l → γg (γf l)) P R
  comp-hom-Large-Poset =
    comp-hom-Large-Preorder
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)
      ( large-preorder-Large-Poset R)
      ( g)
      ( f)
```

### Homotopies of order preserving maps between large posets

Given two order preserving maps `f g : hom-Large-Poset γ P Q` with the same
universe level reindexing `γ`, a **homotopy of order preserving maps** from `f`
to `g` is a pointwise identification of the underlying maps of `f` and `g`.

```agda
module _
  {αP αQ γ : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  where

  htpy-hom-Large-Poset : (f g : hom-Large-Poset γ P Q) → UUω
  htpy-hom-Large-Poset =
    htpy-hom-Large-Preorder
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)

  refl-htpy-hom-Large-Poset :
    (f : hom-Large-Poset γ P Q) → htpy-hom-Large-Poset f f
  refl-htpy-hom-Large-Poset =
    refl-htpy-hom-Large-Preorder
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)
```

## Properties

### Composition of order preserving maps is associative

```agda
module _
  {αP αQ αR αS γh γg γf : Level → Level} {βP βQ βR βS : Level → Level → Level}
  (P : Large-Poset αP βP)
  (Q : Large-Poset αQ βQ)
  (R : Large-Poset αR βR)
  (S : Large-Poset αS βS)
  (h : hom-Large-Poset γh R S)
  (g : hom-Large-Poset γg Q R)
  (f : hom-Large-Poset γf P Q)
  where

  associative-comp-hom-Large-Poset :
    htpy-hom-Large-Poset P S
      ( comp-hom-Large-Poset P Q S (comp-hom-Large-Poset Q R S h g) f)
      ( comp-hom-Large-Poset P R S h (comp-hom-Large-Poset P Q R g f))
  associative-comp-hom-Large-Poset =
    associative-comp-hom-Large-Preorder
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)
      ( large-preorder-Large-Poset R)
      ( large-preorder-Large-Poset S)
      ( h)
      ( g)
      ( f)

  inv-associative-comp-hom-Large-Poset :
    htpy-hom-Large-Poset P S
      ( comp-hom-Large-Poset P R S h (comp-hom-Large-Poset P Q R g f))
      ( comp-hom-Large-Poset P Q S (comp-hom-Large-Poset Q R S h g) f)
  inv-associative-comp-hom-Large-Poset =
    inv-associative-comp-hom-Large-Preorder
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)
      ( large-preorder-Large-Poset R)
      ( large-preorder-Large-Poset S)
      ( h)
      ( g)
      ( f)
```

### Composition of order preserving maps satisfies left and right unit laws

```agda
module _
  {αP αQ γf : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP)
  (Q : Large-Poset αQ βQ)
  (f : hom-Large-Poset γf P Q)
  where

  left-unit-law-comp-hom-Large-Poset :
    htpy-hom-Large-Poset P Q
      ( comp-hom-Large-Poset P Q Q (id-hom-Large-Poset Q) f)
      ( f)
  left-unit-law-comp-hom-Large-Poset =
    left-unit-law-comp-hom-Large-Preorder
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)
      ( f)

  right-unit-law-comp-hom-Large-Poset :
    htpy-hom-Large-Poset P Q
      ( comp-hom-Large-Poset P P Q f (id-hom-Large-Poset P))
      ( f)
  right-unit-law-comp-hom-Large-Poset =
    right-unit-law-comp-hom-Large-Preorder
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)
      ( f)
```

### Order preserving maps preserve similarity of elements

```agda
module _
  {αP αQ γf : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP)
  (Q : Large-Poset αQ βQ)
  (f : hom-Large-Poset γf P Q)
  where

  preserves-sim-hom-Large-Poset :
    {l1 l2 : Level} (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
    sim-Large-Poset P x y →
    sim-Large-Poset Q
      ( map-hom-Large-Poset P Q f x)
      ( map-hom-Large-Poset P Q f y)
  preserves-sim-hom-Large-Poset =
    preserves-sim-hom-Large-Preorder
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)
      ( f)
```

## See also

- [Order preserving maps](order-theory.order-preserving-maps-large-posets.md)
  between large posets
- [Similarity](order-theory.similarity-of-order-preserving-maps-large-posets.md)
  of order preserving maps between large posets
