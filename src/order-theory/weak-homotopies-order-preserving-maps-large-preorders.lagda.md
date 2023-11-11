# Weak homotopies of order preserving maps between large preorders

```agda
module order-theory.weak-homotopies-order-preserving-maps-large-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.universe-levels

open import order-theory.large-preorders
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.similarity-of-elements-large-preorders
```

</details>

## Idea

Consider two order preserving maps `f : hom-Large-Preorder γf P Q` and
`g : hom-Large-Preorder γg P Q` between the same two large preorders `P` and
`Q`, but each specified with their own universe level reindexing functions. We
say that `f` and `g` are **weakly homotopic** if the values `f x` and `g x` are
[similar](order-theory.similarity-of-elements-large-preorders.md) for each
`x : P`. In other words, a **weak homotopy of order preserving maps** between
`f` and `g` consists of an assignment `x ↦ h x` where

```text
  h x : (f x ≤ g x) ∧ (g x ≤ f x)
```

for each `x : type-Large-Preorder P`.

## Definitions

### Weak homotopies of order preserving maps between large preorders

```agda
module _
  {αP αQ γf γg : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Preorder αP βP)
  (Q : Large-Preorder αQ βQ)
  (f : hom-Large-Preorder γf P Q)
  (g : hom-Large-Preorder γg P Q)
  where

  weak-htpy-hom-Large-Preorder : UUω
  weak-htpy-hom-Large-Preorder =
    {l : Level} (x : type-Large-Preorder P l) →
    sim-Large-Preorder Q
      ( map-hom-Large-Preorder f x)
      ( map-hom-Large-Preorder g x)
```

### The reflexive weak homotopy of order preserving maps between large preorders

```agda
module _
  {αP αQ γf : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Preorder αP βP)
  (Q : Large-Preorder αQ βQ)
  (f : hom-Large-Preorder γf P Q)
  where

  refl-weak-htpy-hom-Large-Preorder : weak-htpy-hom-Large-Preorder P Q f f
  refl-weak-htpy-hom-Large-Preorder x =
    refl-sim-Large-Preorder Q (map-hom-Large-Preorder f x)
```

## Properties

### Homotopic order preserving maps are weakly homotopic

```agda
module _
  {αP αQ γ : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Preorder αP βP)
  (Q : Large-Preorder αQ βQ)
  (f : hom-Large-Preorder γ P Q)
  (g : hom-Large-Preorder γ P Q)
  where

  weak-htpy-htpy-hom-Large-Preorder :
    htpy-hom-Large-Preorder P Q f g → weak-htpy-hom-Large-Preorder P Q f g
  weak-htpy-htpy-hom-Large-Preorder H x = sim-eq-Large-Preorder Q (H x)
```
