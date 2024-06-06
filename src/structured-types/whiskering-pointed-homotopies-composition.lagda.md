# Whiskering of pointed homotopies with respect to composition of pointed maps

```agda
module structured-types.whiskering-pointed-homotopies-composition where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.commuting-triangles-of-identifications
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-identifications-concatenation

open import structured-types.pointed-2-homotopies
open import structured-types.pointed-families-of-types
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

The [whiskering operations](foundation.whiskering-operations.md) of
[pointed homotopies](structured-types.pointed-homotopies.md) with respect to
composition of [pointed maps](structured-types.pointed-maps.md) are two
operations that produce pointed homotopies between composites of pointed maps
from either a pointed homotopy on the left or on the right of the composition.

- Consider a pointed homotopy `H : f ~∗ g` between pointed maps `f g : A →∗ B`,
  and consider a pointed map `h : B →∗ C`, as indicated in the diagram

  ```text
        f
      ─────>     h
    A ─────> B ─────> C.
        g
  ```

  The
  {{#concept "left whiskering operation on pointed homotopies" Agda=left-whisker-comp-pointed-htpy}}
  of `h` and `H` is a pointed homotopy

  ```text
    h ·l∗ H : h ∘∗ f ~∗ h ∘∗ g.
  ```

- Consider a pointed map `f : A →∗ B` and consider a pointed homotopy
  `H : g ~∗ g` between tw pointed maps `g h : B →∗ C`, as indicated in the
  diagram

  ```text
                 g
        f      ─────>
    A ─────> B ─────> C.
                 h
  ```

  The
  {{#concept "right whiskering operation on pointed homotopies" Agda=right-whisker-comp-pointed-htpy}}
  of `H` and `f` is a pointed homotopy

  ```text
    H ·r∗ f : g ∘∗ f ~∗ h ∘∗ f.
  ```

## Definitions

### Left whiskering of pointed homotopies

Consider two pointed maps `f := (f₀ , f₁) : A →∗ B` and
`g := (g₀ , g₁) : A →∗ B` equipped with a pointed homotopy
`H := (H₀ , H₁) : f ~∗ g`, and consider furthermore a pointed map
`h := (h₀ , h₁) : B →∗ C`. Then we construct a pointed homotopy

```text
  h ·l∗ H : (h ∘∗ f) ~∗ (h ∘∗ g).
```

**Construction.** The underlying homotopy of `h ·l∗ H` is the whiskered homotpy

```text
  h₀ ·l H₀.
```

For the coherence, we have to show that the triangle

```text
            ap h₀ (H₀ *)
  h₀ (f₀ *) ────────────> h₀ (g₀ *)
           ╲             ╱
   ap h₀ f₁ ╲           ╱ ap h₀ g₁
             ∨         ∨
           h₀ *       h₀ *
               ╲     ╱
             h₁ ╲   ╱ h₁
                 ∨ ∨
                  ∗
```

commutes. By right whiskering of
[commuting triangles of identifications](foundation.commuting-squares-of-identifications.md)
with respect to concatenation it suffices to show that the triangle

```text
           ap h₀ (H₀ *)
  h₀ (f₀ *) ─────────> h₀ (g₀ *)
           ╲          ╱
   ap h₀ f₁ ╲        ╱ ap h₀ g₁
             ╲      ╱
              ∨    ∨
               h₀ *
```

commutes. By functoriality of commuting triangles of identifications, this
follows from the fact that the triangle

```text
        H₀ *
  f₀ * ──────> g₀ *
      ╲       ╱
    f₁ ╲     ╱ g₁
        ╲   ╱
         ∨ ∨
          *
```

commutes.

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  (h : B →∗ C) (f g : A →∗ B) (H : f ~∗ g)
  where

  htpy-left-whisker-comp-pointed-htpy :
    map-comp-pointed-map h f ~ map-comp-pointed-map h g
  htpy-left-whisker-comp-pointed-htpy =
    map-pointed-map h ·l htpy-pointed-htpy H

  coherence-point-left-whisker-comp-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-Π
      ( h ∘∗ f)
      ( h ∘∗ g)
      ( htpy-left-whisker-comp-pointed-htpy)
  coherence-point-left-whisker-comp-pointed-htpy =
    right-whisker-concat-coherence-triangle-identifications
      ( ap (map-pointed-map h) (preserves-point-pointed-map f))
      ( ap (map-pointed-map h) (preserves-point-pointed-map g))
      ( ap
        ( map-pointed-map h)
        ( htpy-pointed-htpy H (point-Pointed-Type A)))
      ( preserves-point-pointed-map h)
      ( map-coherence-triangle-identifications
        ( map-pointed-map h)
        ( preserves-point-pointed-map f)
        ( preserves-point-pointed-map g)
        ( htpy-pointed-htpy H (point-Pointed-Type A))
        ( coherence-point-pointed-htpy H))

  left-whisker-comp-pointed-htpy : h ∘∗ f ~∗ h ∘∗ g
  pr1 left-whisker-comp-pointed-htpy =
    htpy-left-whisker-comp-pointed-htpy
  pr2 left-whisker-comp-pointed-htpy =
    coherence-point-left-whisker-comp-pointed-htpy
```

### Right whiskering of pointed homotopies

Consider a pointed map `f := (f₀ , f₁) : A →∗ B` and two pointed maps
`g := (g₀ , g₁) : B →∗ C` and `h := (h₀ , h₁) : B →∗ C` equipped with a pointed
homotopy `H := (H₀ , H₁) : g ~∗ h`. Then we construct a pointed homotopy

```text
  H ·r∗ f : (g ∘∗ f) ~∗ (h ∘∗ f).
```

**Construction.** The underlying homotopy of `H ·r∗ f` is the homotopy

```text
  H₀ ·r f₀ : (g₀ ∘ f₀) ~ (h₀ ∘ f₀).
```

Then we have to show that the outer triangle in the diagram

```text
              H₀ (f₀ *)
  g₀ (f₀ *) ────────────> h₀ (f₀ *)
           ╲             ╱
   ap g₀ f₁ ╲           ╱ ap h₀ f₁
             ∨  H₀ *   ∨
           g₀ * ────> h₀ *
               ╲     ╱
             g₁ ╲   ╱ h₁
                 ∨ ∨
                  ∗
```

commutes. This is done by vertically pasting the upper square and the lower
triangle. The upper square commutes by inverse naturality of the homotopy `H₀`.
The lower triangle is the base point coherence `H₁` of the pointed homotopy
`H ≐ (H₀ , H₁)`.

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  (g1 g2 : B →∗ C) (H : g1 ~∗ g2) (f : A →∗ B)
  where

  htpy-right-whisker-comp-pointed-htpy :
    unpointed-htpy-pointed-Π (g1 ∘∗ f) (g2 ∘∗ f)
  htpy-right-whisker-comp-pointed-htpy =
    htpy-pointed-htpy H ·r map-pointed-map f

  coherence-point-right-whisker-comp-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-Π
      ( g1 ∘∗ f)
      ( g2 ∘∗ f)
      ( htpy-right-whisker-comp-pointed-htpy)
  coherence-point-right-whisker-comp-pointed-htpy =
    vertical-pasting-coherence-square-coherence-triangle-identifications
      ( htpy-pointed-htpy H _)
      ( ap (map-pointed-map g1) _)
      ( ap (map-pointed-map g2) _)
      ( htpy-pointed-htpy H _)
      ( preserves-point-pointed-map g1)
      ( preserves-point-pointed-map g2)
      ( inv-nat-htpy (htpy-pointed-htpy H) _)
      ( coherence-point-pointed-htpy H)

  right-whisker-comp-pointed-htpy : g1 ∘∗ f ~∗ g2 ∘∗ f
  pr1 right-whisker-comp-pointed-htpy =
    htpy-right-whisker-comp-pointed-htpy
  pr2 right-whisker-comp-pointed-htpy =
    coherence-point-right-whisker-comp-pointed-htpy
```

## Properties

### Computing the left whiskering of the reflexive pointed homotopy

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  (h : B →∗ C) (f : A →∗ B)
  where

  compute-refl-left-whisker-comp-pointed-htpy :
    pointed-2-htpy
      ( left-whisker-comp-pointed-htpy h f f (refl-pointed-htpy f))
      ( refl-pointed-htpy (h ∘∗ f))
  compute-refl-left-whisker-comp-pointed-htpy =
    refl-pointed-2-htpy (refl-pointed-htpy (h ∘∗ f))
```

### Computing the right whiskering of the reflexive pointed homotopy

Consider two pointed maps `f := (f₀ , f₁) : A →∗ B` and
`g := (g₀ , g₁) : B →∗ C`. We are constructing a pointed `2`-homotopy

```text
  right-whisker-comp-pointed-htpy (refl-pointed-htpy h) f ~∗
  refl-pointed-htpy (g ∘∗ f)
```

The underlying homotopy of this pointed `2`-homotopy is `refl-htpy`. The base
point coherence of this homotopy is an identification witnessing that the
triangle

```text
                   H₁
  ap g₀ f₁ ∙ g₁ ──────> refl ∙ (ap g₀ f₁ ∙ g₁)
               ╲       ╱
           refl ╲     ╱ right-whisker-concat refl (ap g₀ f₁ ∙ g₁) ≐ refl
                 ╲   ╱
                  ∨ ∨
       refl ∙ (ap g₀ f₁ ∙ g₁)
```

commutes. Here, the identification `H₁` is the vertical pasting of the upper
square and the lower triangle in the diagram

```text
                refl
  g₀ (f₀ *) ────────────> g₀ (f₀ *)
           ╲             ╱
   ap g₀ f₁ ╲           ╱ ap g₀ f₁
             ∨  refl   ∨
           g₀ * ────> g₀ *
               ╲     ╱
             g₁ ╲   ╱ g₁
                 ∨ ∨
                  ∗.
```

The upper square in this diagram is the inverse naturality of the reflexive
homotopy `refl-htpy` and the lower triangle in this diagram is the reflexive
identification.

Recall that the inverse naturality of the reflexive homotopy
`inv-nat-htpy refl-htpy f₁` computes to the horizontally constant square of
identifications. Furthermore, the vertical pasting of the horizontally constant
square `right-unit` and any commuting triangle `refl` computes to `refl`.
Therefore it follows that the identification `H₁` above is equal to `refl`, as
was required to show.

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  (h : B →∗ C) (f : A →∗ B)
  where

  htpy-compute-refl-right-whisker-comp-pointed-htpy :
    unpointed-htpy-pointed-htpy
      ( right-whisker-comp-pointed-htpy h h (refl-pointed-htpy h) f)
      ( refl-pointed-htpy (h ∘∗ f))
  htpy-compute-refl-right-whisker-comp-pointed-htpy = refl-htpy

  coherence-point-compute-refl-right-whisker-comp-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-htpy
      ( right-whisker-comp-pointed-htpy h h (refl-pointed-htpy h) f)
      ( refl-pointed-htpy (h ∘∗ f))
      ( htpy-compute-refl-right-whisker-comp-pointed-htpy)
  coherence-point-compute-refl-right-whisker-comp-pointed-htpy =
    inv
      ( ( right-unit) ∙
        ( ( ap
            ( λ t →
              vertical-pasting-coherence-square-coherence-triangle-identifications
                ( refl)
                ( ap (map-pointed-map h) (preserves-point-pointed-map f))
                ( ap (map-pointed-map h) (preserves-point-pointed-map f))
                ( refl)
                ( preserves-point-pointed-map h)
                ( preserves-point-pointed-map h)
                ( t)
                ( refl))
            ( inv-nat-refl-htpy
              ( map-pointed-map h)
              ( preserves-point-pointed-map f))) ∙
          ( right-whisker-concat-horizontal-refl-coherence-square-identifications
            ( ap (map-pointed-map h) (preserves-point-pointed-map f))
            ( preserves-point-pointed-map h))))

  compute-refl-right-whisker-comp-pointed-htpy :
    pointed-2-htpy
      ( right-whisker-comp-pointed-htpy h h (refl-pointed-htpy h) f)
      ( refl-pointed-htpy (h ∘∗ f))
  pr1 compute-refl-right-whisker-comp-pointed-htpy =
    htpy-compute-refl-right-whisker-comp-pointed-htpy
  pr2 compute-refl-right-whisker-comp-pointed-htpy =
    coherence-point-compute-refl-right-whisker-comp-pointed-htpy
```
