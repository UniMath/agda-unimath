# Similarity of order preserving maps between large posets

```agda
open import foundation.function-extensionality-axiom

module
  order-theory.similarity-of-order-preserving-maps-large-posets
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext
open import foundation.universe-levels

open import order-theory.large-posets funext
open import order-theory.order-preserving-maps-large-posets funext
open import order-theory.similarity-of-elements-large-posets funext
open import order-theory.similarity-of-order-preserving-maps-large-preorders funext
```

</details>

## Idea

Consider two
[order preserving maps](order-theory.order-preserving-maps-large-posets.md)
`f : hom-Large-Poset γf P Q` and `g : hom-Large-Poset γg P Q` between the same
two [large posets](order-theory.large-posets.md) `P` and `Q`, but each specified
with their own universe level reindexing functions. We say that `f` and `g` are
**similar** if the values `f x` and `g x` are
[similar](order-theory.similarity-of-elements-large-posets.md) for each `x : P`.
In other words, a **similarity of order preserving maps** between `f` and `g`
consists of an assignment `x ↦ h x` where

```text
  h x : f x ≈ g x
```

for each `x : type-Large-Poset P`. In informal writing we will use the notation
`f ≈ g` to assert that the order preserving map `f` is similar to the order
preserving map `g`.

## Definitions

### Similarity of order preserving maps between large posets

```agda
module _
  {αP αQ γf γg : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP)
  (Q : Large-Poset αQ βQ)
  (f : hom-Large-Poset γf P Q)
  (g : hom-Large-Poset γg P Q)
  where

  sim-hom-Large-Poset : UUω
  sim-hom-Large-Poset =
    sim-hom-Large-Preorder
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)
      ( f)
      ( g)
```

### The reflexive similarity of order preserving maps between large posets

```agda
module _
  {αP αQ γf : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP)
  (Q : Large-Poset αQ βQ)
  (f : hom-Large-Poset γf P Q)
  where

  refl-sim-hom-Large-Poset : sim-hom-Large-Poset P Q f f
  refl-sim-hom-Large-Poset =
    refl-sim-hom-Large-Preorder
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)
      ( f)
```

## Properties

### Order preserving maps with the same universe level reindexing function are homotopic if and only if they are similar

```agda
module _
  {αP αQ γ : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP)
  (Q : Large-Poset αQ βQ)
  (f : hom-Large-Poset γ P Q)
  (g : hom-Large-Poset γ P Q)
  where

  sim-htpy-hom-Large-Poset :
    htpy-hom-Large-Poset P Q f g → sim-hom-Large-Poset P Q f g
  sim-htpy-hom-Large-Poset =
    sim-htpy-hom-Large-Preorder
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)
      ( f)
      ( g)

  htpy-sim-hom-Large-Poset :
    sim-hom-Large-Poset P Q f g → htpy-hom-Large-Poset P Q f g
  htpy-sim-hom-Large-Poset H x =
    eq-sim-Large-Poset Q
      ( map-hom-Large-Poset P Q f x)
      ( map-hom-Large-Poset P Q g x)
      ( H x)
```
