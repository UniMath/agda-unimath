# Whiskering of pointed homotopies

```agda
module structured-types.whiskering-pointed-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies

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

Consider two pointed maps `f1 f2 : A →∗ B` equipped with a pointed homotopy `H : f1 ~∗ f2`, and a pointed map `g : B →∗ C`. Then we construct a pointed homotopy

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

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  (g : B →∗ C) (f1 f2 : A →∗ B) (H : htpy-pointed-map f1 f2)
  where

  htpy-left-whisker-pointed-htpy :
    map-comp-pointed-map g f1 ~ map-comp-pointed-map g f2
  htpy-left-whisker-pointed-htpy =
    map-pointed-map g ·l htpy-pointed-htpy f1 f2 H

  coh-left-whisker-pointed-htpy' :
    coherence-triangle-pointed-htpy'
      ( g ∘∗ f1)
      ( g ∘∗ f2)
      ( htpy-left-whisker-pointed-htpy)
  coh-left-whisker-pointed-htpy' =
    ( ap
      ( concat' _ (preserves-point-pointed-map g))
      {!!}) ∙
    ( assoc
      ( ap (map-pointed-map g) (htpy-pointed-htpy f1 f2 H _))
      ( ap (map-pointed-map g) (preserves-point-pointed-map f2))
      ( preserves-point-pointed-map g))

  coh-left-whisker-pointed-htpy :
    coherence-triangle-pointed-htpy
      ( g ∘∗ f1)
      ( g ∘∗ f2)
      ( htpy-left-whisker-pointed-htpy)
  coh-left-whisker-pointed-htpy =
    ( ( ( ap (ap (map-pointed-map g)) (coh-pointed-htpy f1 f2 H)) ∙
        ( ap-concat
          ( map-pointed-map g)
          ( preserves-point-pointed-map f1)
          ( inv (preserves-point-pointed-map f2)))) ∙
      ( ap
        ( concat
          ( ap (map-pointed-map g) (preserves-point-pointed-map f1))
          ( map-pointed-map g
            ( map-pointed-map f2 (point-Pointed-Type A))))
        ( ( ( ( ap-inv
                ( map-pointed-map g)
                ( preserves-point-pointed-map f2)) ∙
              ( ap
                ( concat'
                  ( map-pointed-map g
                    ( point-Pointed-Fam A (constant-Pointed-Fam A B)))
                  ( inv
                    ( ap
                      ( map-pointed-map g)
                      ( preserves-point-pointed-map f2)))))
              ( inv (right-inv (preserves-point-pointed-map g)))) ∙
            ( assoc
              ( preserves-point-pointed-map g)
              ( inv (preserves-point-pointed-map g))
              ( inv
                ( ap
                  ( map-pointed-map g)
                  ( preserves-point-pointed-map f2))))) ∙
          ( ap
            ( concat
              ( preserves-point-pointed-map g)
              ( map-pointed-map g
                ( map-pointed-map f2 (point-Pointed-Type A))))
            ( inv
              ( distributive-inv-concat
                ( ap (map-pointed-map g) (preserves-point-pointed-map f2))
                ( preserves-point-pointed-map g))))))) ∙
    ( inv
      ( assoc
        ( ap (map-pointed-map g) (preserves-point-pointed-map f1))
        ( preserves-point-pointed-map g)
        ( inv
          ( ( ap
              ( map-pointed-map g)
              ( preserves-point-pointed-map f2)) ∙
            ( preserves-point-pointed-map g)))))

  left-whisker-pointed-htpy :
    htpy-pointed-map
      ( comp-pointed-map g f1)
      ( comp-pointed-map g f2)
  pr1 left-whisker-pointed-htpy = htpy-left-whisker-pointed-htpy
  pr2 left-whisker-pointed-htpy = coh-left-whisker-pointed-htpy
```

### Right whiskering of pointed homotopies

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  where

  right-whisker-htpy-pointed-map :
    (g1 g2 : B →∗ C) (H : htpy-pointed-map g1 g2) (f : A →∗ B) →
    htpy-pointed-map (comp-pointed-map g1 f) (comp-pointed-map g2 f)
  right-whisker-htpy-pointed-map g1 g2 H (pair f refl) =
    pair (htpy-pointed-htpy g1 g2 H ·r f) (coh-pointed-htpy g1 g2 H)
```
