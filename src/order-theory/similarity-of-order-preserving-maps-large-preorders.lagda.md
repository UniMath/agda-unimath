# Similarity of order preserving maps between large preorders

```agda
module order-theory.similarity-of-order-preserving-maps-large-preorders where
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

Consider two
[order preserving maps](order-theory.order-preserving-maps-large-preorders.md)
`f : hom-Large-Preorder γf P Q` and `g : hom-Large-Preorder γg P Q` between the
same two [large preorders](order-theory.large-preorders.md) `P` and `Q`, but
each specified with their own universe level reindexing functions. We say that
`f` and `g` are **similar** if the values `f x` and `g x` are
[similar](order-theory.similarity-of-elements-large-preorders.md) for each
`x : P`. In other words, a **similarity of order preserving maps** between `f`
and `g` consists of an assignment `x ↦ h x` where

```text
  h x : f x ≍ g x
```

for each `x : type-Large-Preorder P`. In informal writing we will use the
notation `f ≍ g` to assert that the order preserving map `f` is similar to the
order preserving map `g`. The symbol `≍` is the unicode symbol
[Equivalent To](https://codepoints.net/U+224d) (agda-input: `\asymp`).

## Definitions

### Similarities of order preserving maps between large preorders

```agda
module _
  {αP αQ γf γg : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Preorder αP βP)
  (Q : Large-Preorder αQ βQ)
  (f : hom-Large-Preorder γf P Q)
  (g : hom-Large-Preorder γg P Q)
  where

  sim-hom-Large-Preorder : UUω
  sim-hom-Large-Preorder =
    {l : Level} (x : type-Large-Preorder P l) →
    sim-Large-Preorder Q
      ( map-hom-Large-Preorder f x)
      ( map-hom-Large-Preorder g x)
```

### The reflexive similarity of order preserving maps between large preorders

```agda
module _
  {αP αQ γf : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Preorder αP βP)
  (Q : Large-Preorder αQ βQ)
  (f : hom-Large-Preorder γf P Q)
  where

  refl-sim-hom-Large-Preorder : sim-hom-Large-Preorder P Q f f
  refl-sim-hom-Large-Preorder x =
    refl-sim-Large-Preorder Q (map-hom-Large-Preorder f x)
```

## Properties

### Homotopic order preserving maps are similar

```agda
module _
  {αP αQ γ : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Preorder αP βP)
  (Q : Large-Preorder αQ βQ)
  (f : hom-Large-Preorder γ P Q)
  (g : hom-Large-Preorder γ P Q)
  where

  sim-htpy-hom-Large-Preorder :
    htpy-hom-Large-Preorder P Q f g → sim-hom-Large-Preorder P Q f g
  sim-htpy-hom-Large-Preorder H x = sim-eq-Large-Preorder Q (H x)
```
