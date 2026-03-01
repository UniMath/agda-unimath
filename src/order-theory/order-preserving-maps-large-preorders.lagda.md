# Order preserving maps between large preorders

```agda
module order-theory.order-preserving-maps-large-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies

open import order-theory.large-preorders
open import order-theory.order-preserving-maps-preorders
open import order-theory.similarity-of-elements-large-preorders
```

</details>

## Idea

An **order preserving map** between
[large preorders](order-theory.large-preorders.md) `P` and `Q` consists of a map

```text
  f : type-Large-Preorder P l1 → type-Large-Preorder Q (γ l1)
```

for each [universe level](foundation.universe-levels.md) `l1`, such that `x ≤ y`
implies `f x ≤ f y` for any two elements `x y : P`. The function
`γ : Level → Level` that specifies the universe level of `f x` in terms of the
universe level of `x` is called the **universe level reindexing function** of
the order preserving map `f`.

## Definitions

### The predicate that a map between large preorders is order preserving

```agda
module _
  {αP αQ : Level → Level} {βP βQ : Level → Level → Level} {γ : Level → Level}
  (P : Large-Preorder αP βP) (Q : Large-Preorder αQ βQ)
  where

  preserves-order-map-Large-Preorder :
    ({l : Level} → type-Large-Preorder P l → type-Large-Preorder Q (γ l)) →
    UUω
  preserves-order-map-Large-Preorder f =
    {l1 l2 : Level}
    (x : type-Large-Preorder P l1) (y : type-Large-Preorder P l2) →
    leq-Large-Preorder P x y → leq-Large-Preorder Q (f x) (f y)
```

### The type of order preserving maps between large preorders

```agda
module _
  {αP αQ : Level → Level} {βP βQ : Level → Level → Level}
  (γ : Level → Level)
  (P : Large-Preorder αP βP) (Q : Large-Preorder αQ βQ)
  where

  record hom-Large-Preorder : UUω
    where
    eta-equality
    constructor
      make-hom-Large-Preorder
    field
      map-hom-Large-Preorder :
        {l1 : Level} → type-Large-Preorder P l1 → type-Large-Preorder Q (γ l1)
      preserves-order-hom-Large-Preorder :
        preserves-order-map-Large-Preorder P Q map-hom-Large-Preorder

  open hom-Large-Preorder public
```

### The induced order preserving maps between small preorders

```agda
module _
  {αP αQ : Level → Level} {βP βQ : Level → Level → Level} {γ : Level → Level}
  (P : Large-Preorder αP βP)
  (Q : Large-Preorder αQ βQ)
  (f : hom-Large-Preorder γ P Q)
  where

  hom-preorder-hom-Large-Preorder :
    (l : Level) →
    hom-Preorder
      ( preorder-Large-Preorder P l)
      ( preorder-Large-Preorder Q (γ l))
  hom-preorder-hom-Large-Preorder l =
    ( map-hom-Large-Preorder f , preserves-order-hom-Large-Preorder f)
```

### The identity order preserving map on a large preorder

```agda
module _
  {αP : Level → Level} {βP : Level → Level → Level} (P : Large-Preorder αP βP)
  where

  id-hom-Large-Preorder : hom-Large-Preorder (λ l → l) P P
  map-hom-Large-Preorder id-hom-Large-Preorder = id
  preserves-order-hom-Large-Preorder id-hom-Large-Preorder x y = id
```

### Composition of order preserving maps between large preorders

```agda
module _
  {αP αQ αR γg γf : Level → Level} {βP βQ βR : Level → Level → Level}
  (P : Large-Preorder αP βP)
  (Q : Large-Preorder αQ βQ)
  (R : Large-Preorder αR βR)
  (g : hom-Large-Preorder γg Q R)
  (f : hom-Large-Preorder γf P Q)
  where

  map-comp-hom-Large-Preorder :
    {l1 : Level} → type-Large-Preorder P l1 → type-Large-Preorder R (γg (γf l1))
  map-comp-hom-Large-Preorder =
    map-hom-Large-Preorder g ∘ map-hom-Large-Preorder f

  preserves-order-comp-hom-Large-Preorder :
    preserves-order-map-Large-Preorder P R map-comp-hom-Large-Preorder
  preserves-order-comp-hom-Large-Preorder x y =
    preserves-order-hom-Large-Preorder g _ _ ∘
    preserves-order-hom-Large-Preorder f _ _

  comp-hom-Large-Preorder : hom-Large-Preorder (λ l → γg (γf l)) P R
  map-hom-Large-Preorder comp-hom-Large-Preorder =
    map-comp-hom-Large-Preorder
  preserves-order-hom-Large-Preorder comp-hom-Large-Preorder =
    preserves-order-comp-hom-Large-Preorder
```

### Homotopies of order preserving maps between large preorders

Given two order preserving maps `f g : hom-Large-Preorder γ P Q` with the same
universe level reindexing `γ`, a **homotopy of order preserving maps** from `f`
to `g` is a pointwise identification of the underlying maps of `f` and `g`.

```agda
module _
  {αP αQ γ : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Preorder αP βP) (Q : Large-Preorder αQ βQ)
  where

  htpy-hom-Large-Preorder : (f g : hom-Large-Preorder γ P Q) → UUω
  htpy-hom-Large-Preorder f g =
    {l : Level} → map-hom-Large-Preorder f {l} ~ map-hom-Large-Preorder g {l}

  refl-htpy-hom-Large-Preorder :
    (f : hom-Large-Preorder γ P Q) → htpy-hom-Large-Preorder f f
  refl-htpy-hom-Large-Preorder f = refl-htpy
```

## Properties

### Composition of order preserving maps is associative

```agda
module _
  {αP αQ αR αS γh γg γf : Level → Level} {βP βQ βR βS : Level → Level → Level}
  (P : Large-Preorder αP βP)
  (Q : Large-Preorder αQ βQ)
  (R : Large-Preorder αR βR)
  (S : Large-Preorder αS βS)
  (h : hom-Large-Preorder γh R S)
  (g : hom-Large-Preorder γg Q R)
  (f : hom-Large-Preorder γf P Q)
  where

  associative-comp-hom-Large-Preorder :
    htpy-hom-Large-Preorder P S
      ( comp-hom-Large-Preorder P Q S (comp-hom-Large-Preorder Q R S h g) f)
      ( comp-hom-Large-Preorder P R S h (comp-hom-Large-Preorder P Q R g f))
  associative-comp-hom-Large-Preorder = refl-htpy
```

### Composition of order preserving maps satisfies left and right unit laws

```agda
module _
  {αP αQ γf : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Preorder αP βP)
  (Q : Large-Preorder αQ βQ)
  (f : hom-Large-Preorder γf P Q)
  where

  left-unit-law-comp-hom-Large-Preorder :
    htpy-hom-Large-Preorder P Q
      ( comp-hom-Large-Preorder P Q Q (id-hom-Large-Preorder Q) f)
      ( f)
  left-unit-law-comp-hom-Large-Preorder = refl-htpy

  right-unit-law-comp-hom-Large-Preorder :
    htpy-hom-Large-Preorder P Q
      ( comp-hom-Large-Preorder P P Q f (id-hom-Large-Preorder P))
      ( f)
  right-unit-law-comp-hom-Large-Preorder = refl-htpy
```

### Order preserving maps preserve similarity of elements

```agda
module _
  {αP αQ γf : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Preorder αP βP)
  (Q : Large-Preorder αQ βQ)
  (f : hom-Large-Preorder γf P Q)
  where

  preserves-sim-hom-Large-Preorder :
    {l1 l2 : Level}
    (x : type-Large-Preorder P l1) (y : type-Large-Preorder P l2) →
    sim-Large-Preorder P x y →
    sim-Large-Preorder Q
      ( map-hom-Large-Preorder f x)
      ( map-hom-Large-Preorder f y)
  pr1 (preserves-sim-hom-Large-Preorder x y (s , t)) =
    preserves-order-hom-Large-Preorder f x y s
  pr2 (preserves-sim-hom-Large-Preorder x y (s , t)) =
    preserves-order-hom-Large-Preorder f y x t
```

## See also

- [Order preserving maps](order-theory.order-preserving-maps-large-posets.md)
  between large posets
- [Similarity](order-theory.similarity-of-order-preserving-maps-large-preorders.md)
  of order preserving maps between large preorders
