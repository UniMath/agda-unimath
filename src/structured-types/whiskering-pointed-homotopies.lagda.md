# Whiskering of pointed homotopies

```agda
module structured-types.whiskering-pointed-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-identifications
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-identifications-concatenation

open import structured-types.pointed-families-of-types
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

Consider a [pointed homotopy](structured-types.pointed-homotopies.md)
`H : f ~∗ g` between [pointed maps](structured-types.pointed-maps.md)
`f g : A →∗ B`, and consider a pointed map `h : B →∗ C`, as indicated in the
diagram

```text
      f
    ----->     h
  A -----> B -----> C.
      g
```

The {{#concept "left whiskering operation on pointed homotopies"}} takes a
pointed homotopy `H` and a pointed map `f` and returns a pointed homotopy

```text
  h ·l∗ H : h ∘∗ f ~∗ h ∘∗ g
```

## Definitions

### Left whiskering of pointed homotopies

Consider two pointed maps `f1 f2 : A →∗ B` equipped with a pointed homotopy
`H : f1 ~∗ f2`, and a pointed map `g : B →∗ C`. Then we construct a pointed
homotopy

```text
  g ·l H : (g ∘∗ f1) ~∗ (g ∘∗ f2)
```

**Proof.** The underlying homotopy of `g ·l H` is the whiskered homotpy

```text
  map-pointed-map g ·l htpy-pointed-htpy f1 f2 H.
```

For the coherence, we have to show that the triangle

```text
                             ap g (H *)
                   g (f1 *) ------------> g (f2 *)
                           \             /
  ap g (preserves-point f1) \           / ap g (preserves-point f2)
                             ∨         ∨
                            g *       g *
                               \     /
              preserves-point g \   / preserves-point g
                                 ∨ ∨
                                  ∗
```

commutes. By right whiskering of
[commuting triangles of identifications](foundation.commuting-squares-of-identifications.md)
with respect to concatenation it suffices to show that the triangle

```text
                            ap g (H *)
                   g (f1 *) --------> g (f2 *)
                           \         /
  ap g (preserves-point f1) \       / ap g (preserves-point f2)
                             \     /
                              ∨   ∨
                               g *
```

commutes. By functoriality of commuting triangles of identifications, this
follows from the fact that the triangle

```text
                       H *
                f1 * ------> f2 *
                    \       /
  preserves-point f1 \     / preserves-point f2
                      \   /
                       ∨ ∨
                        *
```

commutes.

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  (g : B →∗ C) (f1 f2 : A →∗ B) (H : f1 ~∗ f2)
  where

  htpy-left-whisker-pointed-htpy :
    map-comp-pointed-map g f1 ~ map-comp-pointed-map g f2
  htpy-left-whisker-pointed-htpy =
    map-pointed-map g ·l htpy-pointed-htpy f1 f2 H

  coh-left-whisker-pointed-htpy' :
    coherence-base-point-pointed-htpy'
      ( g ∘∗ f1)
      ( g ∘∗ f2)
      ( htpy-left-whisker-pointed-htpy)
  coh-left-whisker-pointed-htpy' =
    right-whisker-concat-coherence-triangle-identifications
      ( ap (map-pointed-map g) (preserves-point-pointed-map f1))
      ( ap (map-pointed-map g) (preserves-point-pointed-map f2))
      ( ap
        ( map-pointed-map g)
        ( htpy-pointed-htpy f1 f2 H (point-Pointed-Type A)))
      ( preserves-point-pointed-map g)
      ( map-coherence-triangle-identifications
        ( map-pointed-map g)
        ( preserves-point-pointed-map f1)
        ( preserves-point-pointed-map f2)
        ( htpy-pointed-htpy f1 f2 H (point-Pointed-Type A))
        ( coh-pointed-htpy' f1 f2 H))

  left-whisker-pointed-htpy : g ∘∗ f1 ~∗ g ∘∗ f2
  left-whisker-pointed-htpy =
    make-pointed-htpy
      ( g ∘∗ f1)
      ( g ∘∗ f2)
      ( htpy-left-whisker-pointed-htpy)
      ( coh-left-whisker-pointed-htpy')
```

### Right whiskering of pointed homotopies

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  where

  right-whisker-pointed-htpy :
    (g1 g2 : B →∗ C) (H : g1  ~∗ g2) (f : A →∗ B) → g1 ∘∗ f ~∗ g2 ∘∗ f
  right-whisker-pointed-htpy g1 g2 H (pair f refl) =
    pair (htpy-pointed-htpy g1 g2 H ·r f) (coh-pointed-htpy g1 g2 H)
```
