# Weak homotopies of order preserving maps between large posets

```agda
module order-theory.weak-homotopies-order-preserving-maps-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.order-preserving-maps-large-posets
open import order-theory.similarity-of-elements-large-posets
open import order-theory.weak-homotopies-order-preserving-maps-large-preorders
```

</details>

## Idea

Consider two order preserving maps `f : hom-Large-Poset γf P Q` and
`g : hom-Large-Poset γg P Q` between the same two large posets `P` and `Q`, but
each specified with their own universe level reindexing functions. We say that
`f` and `g` are **weakly homotopic** if the values `f x` and `g x` are
[similar](order-theory.similarity-of-elements-large-posets.md) for each `x : P`.
In other words, a **weak homotopy of order preserving maps** between `f` and `g`
consists of an assignment `x ↦ h x` where

```text
  h x : (f x ≤ g x) ∧ (g x ≤ f x)
```

for each `x : type-Large-Poset P`.

## Definitions

### Weak homotopies of order preserving maps between large posets

```agda
module _
  {αP αQ γf γg : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP)
  (Q : Large-Poset αQ βQ)
  (f : hom-Large-Poset γf P Q)
  (g : hom-Large-Poset γg P Q)
  where

  weak-htpy-hom-Large-Poset : UUω
  weak-htpy-hom-Large-Poset =
    weak-htpy-hom-Large-Preorder
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)
      ( f)
      ( g)
```

### The reflexive weak homotopy of order preserving maps between large posets

```agda
module _
  {αP αQ γf : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP)
  (Q : Large-Poset αQ βQ)
  (f : hom-Large-Poset γf P Q)
  where

  refl-weak-htpy-hom-Large-Poset : weak-htpy-hom-Large-Poset P Q f f
  refl-weak-htpy-hom-Large-Poset =
    refl-weak-htpy-hom-Large-Preorder
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)
      ( f)
```

## Properties

### Order preserving maps with the same universe level reindexing function are homotopic if and only if they are weakly homotopic

```agda
module _
  {αP αQ γ : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP)
  (Q : Large-Poset αQ βQ)
  (f : hom-Large-Poset γ P Q)
  (g : hom-Large-Poset γ P Q)
  where

  weak-htpy-htpy-hom-Large-Poset :
    htpy-hom-Large-Poset P Q f g → weak-htpy-hom-Large-Poset P Q f g
  weak-htpy-htpy-hom-Large-Poset =
    weak-htpy-htpy-hom-Large-Preorder
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)
      ( f)
      ( g)

  htpy-weak-htpy-hom-Large-Poset :
    weak-htpy-hom-Large-Poset P Q f g → htpy-hom-Large-Poset P Q f g
  htpy-weak-htpy-hom-Large-Poset H x =
    eq-sim-Large-Poset Q
      ( map-hom-Large-Poset P Q f x)
      ( map-hom-Large-Poset P Q g x)
      ( H x)
```
