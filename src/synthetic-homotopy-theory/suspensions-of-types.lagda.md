# Suspensions of types

```agda
module synthetic-homotopy-theory.suspensions-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.connected-types
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-suspension-structures
open import synthetic-homotopy-theory.dependent-universal-property-suspensions
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.universal-property-pushouts
open import synthetic-homotopy-theory.universal-property-suspensions
```

</details>

## Idea

The **suspension** of a type `X` is the
[pushout](synthetic-homotopy-theory.pushouts.md) of the
[span](foundation.spans.md)

```text
unit <-- X --> unit
```

Suspensions play an important role in synthetic homotopy theory. For example,
they star in the freudenthal suspension theorem and give us a definition of
[the spheres](synthetic-homotopy-theory.spheres.md).

## Definition

### The suspension of an ordinary type `X`

```agda
suspension :
  {l : Level} → UU l → UU l
suspension X = pushout (terminal-map {A = X}) (terminal-map {A = X})

north-suspension :
  {l : Level} {X : UU l} → suspension X
north-suspension {X = X} =
  inl-pushout terminal-map terminal-map star

south-suspension :
  {l : Level} {X : UU l} → suspension X
south-suspension {X = X} =
  inr-pushout terminal-map terminal-map star

meridian-suspension :
  {l : Level} {X : UU l} → X →
  Id (north-suspension {X = X}) (south-suspension {X = X})
meridian-suspension {X = X} =
  glue-pushout terminal-map terminal-map

suspension-structure-suspension :
  {l : Level} (X : UU l) → suspension-structure X (suspension X)
pr1 (suspension-structure-suspension X) = north-suspension
pr1 (pr2 (suspension-structure-suspension X)) = south-suspension
pr2 (pr2 (suspension-structure-suspension X)) = meridian-suspension
```

## Properties

### The suspension of X has the universal property of suspensions

```agda
module _
  {l1 : Level} (X : UU l1)
  where

  up-suspension :
    {l : Level} →
    universal-property-suspension l X
      ( suspension X)
      ( suspension-structure-suspension X)
  up-suspension Z =
    is-equiv-htpy
      ( ev-suspension (suspension-structure-suspension X) Z)
      ( triangle-ev-suspension
        { X = X}
        { Y = suspension X}
        ( suspension-structure-suspension X)
        ( Z))
      ( is-equiv-map-equiv
        ( ( equiv-suspension-structure-suspension-cocone X Z) ∘e
          ( equiv-up-pushout terminal-map terminal-map Z)))

  equiv-up-suspension :
    {l : Level} (Z : UU l) → (suspension X → Z) ≃ (suspension-structure X Z)
  pr1 (equiv-up-suspension Z) =
    ev-suspension (suspension-structure-suspension X) Z
  pr2 (equiv-up-suspension Z) = up-suspension Z

  map-inv-up-suspension :
    {l : Level} (Z : UU l) → suspension-structure X Z → suspension X → Z
  map-inv-up-suspension Z =
    map-inv-equiv (equiv-up-suspension Z)

  is-section-map-inv-up-suspension :
    {l : Level} (Z : UU l) →
    ( ( ev-suspension ((suspension-structure-suspension X)) Z) ∘
      ( map-inv-up-suspension Z)) ~ id
  is-section-map-inv-up-suspension Z =
    is-section-map-inv-is-equiv (up-suspension Z)

  is-retraction-map-inv-up-suspension :
    {l : Level} (Z : UU l) →
    ( ( map-inv-up-suspension Z) ∘
      ( ev-suspension ((suspension-structure-suspension X)) Z)) ~ id
  is-retraction-map-inv-up-suspension Z =
    is-retraction-map-inv-is-equiv (up-suspension Z)

  up-suspension-north-suspension :
    {l : Level} (Z : UU l) (c : suspension-structure X Z) →
    ( map-inv-up-suspension Z c north-suspension) ＝
    ( north-suspension-structure c)
  up-suspension-north-suspension Z c =
    pr1 (htpy-eq-suspension-structure (is-section-map-inv-up-suspension Z c))

  up-suspension-south-suspension :
    {l : Level} (Z : UU l) (c : suspension-structure X Z) →
    ( map-inv-up-suspension Z c south-suspension) ＝
    ( south-suspension-structure c)
  up-suspension-south-suspension Z c =
    pr1
      ( pr2
        ( htpy-eq-suspension-structure (is-section-map-inv-up-suspension Z c)))

  up-suspension-meridian-suspension :
    {l : Level} (Z : UU l) (c : suspension-structure X Z) (x : X) →
    ( ( ap (map-inv-up-suspension Z c) (meridian-suspension x)) ∙
      ( up-suspension-south-suspension Z c)) ＝
    ( ( up-suspension-north-suspension Z c) ∙
    ( meridian-suspension-structure c x))
  up-suspension-meridian-suspension Z c =
    pr2
      ( pr2
        ( htpy-eq-suspension-structure (is-section-map-inv-up-suspension Z c)))

  ev-suspension-up-suspension :
    {l : Level} (Z : UU l) (c : suspension-structure X Z) →
    ( ev-suspension
      ( suspension-structure-suspension X)
      ( Z)
      ( map-inv-up-suspension Z c)) ＝ c
  ev-suspension-up-suspension {l} Z c =
    eq-htpy-suspension-structure
      ( ( up-suspension-north-suspension Z c) ,
        ( up-suspension-south-suspension Z c) ,
        ( up-suspension-meridian-suspension Z c))
```

### The suspension of X has the dependent universal property of suspensions

```agda
dependent-up-suspension :
    (l : Level) {l1 : Level} {X : UU l1} →
    dependent-universal-property-suspension
      ( l)
      ( suspension-structure-suspension X)
dependent-up-suspension l {X = X} B =
  is-equiv-htpy
    ( map-equiv
      ( equiv-dependent-suspension-structure-suspension-cocone
        ( suspension-structure-suspension X)
        ( B)) ∘
      ( dependent-cocone-map
        ( terminal-map)
        ( terminal-map)
        ( cocone-suspension-structure
          ( X)
          ( suspension X)
          ( suspension-structure-suspension X))
        ( B)))
    ( inv-htpy
      ( triangle-dependent-ev-suspension
        ( suspension-structure-suspension X)
        ( B)))
    ( is-equiv-comp
      ( map-equiv
        ( equiv-dependent-suspension-structure-suspension-cocone
          ( suspension-structure-suspension X)
          ( B)))
      ( dependent-cocone-map
        ( terminal-map)
        ( terminal-map)
        ( cocone-suspension-structure X
          ( suspension X)
          ( suspension-structure-suspension X))
        ( B))
      ( dependent-up-pushout terminal-map terminal-map B)
      ( is-equiv-map-equiv
        ( equiv-dependent-suspension-structure-suspension-cocone
          ( suspension-structure-suspension X)
          ( B))))

equiv-dependent-up-suspension :
    {l1 l2 : Level} {X : UU l1} (B : suspension X → UU l2) →
    ((x : suspension X) → B x) ≃
    ( dependent-suspension-structure B (suspension-structure-suspension X))
pr1 (equiv-dependent-up-suspension {l2 = l2} {X = X} B) =
  (dependent-ev-suspension (suspension-structure-suspension X) B)
pr2 (equiv-dependent-up-suspension {l2 = l2} B) =
  dependent-up-suspension l2 B

module _
  {l1 l2 : Level} {X : UU l1} (B : suspension X → UU l2)
  where

  map-inv-dependent-up-suspension :
    dependent-suspension-structure B (suspension-structure-suspension X) →
    (x : suspension X) → B x
  map-inv-dependent-up-suspension =
    map-inv-is-equiv (dependent-up-suspension l2 B)

  is-section-map-inv-dependent-up-suspension :
    ( ( dependent-ev-suspension (suspension-structure-suspension X) B) ∘
      ( map-inv-dependent-up-suspension)) ~ id
  is-section-map-inv-dependent-up-suspension =
    is-section-map-inv-is-equiv (dependent-up-suspension l2 B)

  is-retraction-map-inv-dependent-up-suspension :
    ( ( map-inv-dependent-up-suspension) ∘
      ( dependent-ev-suspension (suspension-structure-suspension X) B)) ~ id
  is-retraction-map-inv-dependent-up-suspension =
    is-retraction-map-inv-is-equiv (dependent-up-suspension l2 B)

  dependent-up-suspension-north-suspension :
    (d : dependent-suspension-structure
      ( B)
      ( suspension-structure-suspension X)) →
    ( map-inv-dependent-up-suspension d north-suspension) ＝
    ( north-dependent-suspension-structure d)
  dependent-up-suspension-north-suspension d =
    north-htpy-dependent-suspension-structure
      ( B)
      ( htpy-eq-dependent-suspension-structure
        ( B)
        ( is-section-map-inv-dependent-up-suspension d))

  dependent-up-suspension-south-suspension :
    (d : dependent-suspension-structure
      ( B)
      ( suspension-structure-suspension X)) →
    ( map-inv-dependent-up-suspension d south-suspension) ＝
    ( south-dependent-suspension-structure d)
  dependent-up-suspension-south-suspension d =
    south-htpy-dependent-suspension-structure
      ( B)
      ( htpy-eq-dependent-suspension-structure
        ( B)
        ( is-section-map-inv-dependent-up-suspension d))

  dependent-up-suspension-meridian-suspension :
    (d : dependent-suspension-structure
      ( B)
      ( suspension-structure-suspension X))
    (x : X) →
      coherence-square-identifications
        ( ap
          ( tr B (meridian-suspension x))
          ( dependent-up-suspension-north-suspension d))
        ( apd
          ( map-inv-dependent-up-suspension d)
          ( meridian-suspension x))
        ( meridian-dependent-suspension-structure d x)
        ( dependent-up-suspension-south-suspension d)
  dependent-up-suspension-meridian-suspension d =
    meridian-htpy-dependent-suspension-structure
      ( B)
      ( htpy-eq-dependent-suspension-structure
        ( B)
        ( is-section-map-inv-dependent-up-suspension d))
```

### Characterization of homotopies between functions with domain a suspension

```agda
module _
  {l1 l2 : Level} (X : UU l1) {Y : UU l2}
  (f g : suspension X → Y)
  where

  htpy-function-out-of-suspension : UU (l1 ⊔ l2)
  htpy-function-out-of-suspension =
    htpy-suspension-structure
      ( ev-suspension (suspension-structure-suspension X) Y f)
      ( ev-suspension (suspension-structure-suspension X) Y g)

  north-htpy-function-out-of-suspension :
    htpy-function-out-of-suspension →
    f north-suspension ＝ g north-suspension
  north-htpy-function-out-of-suspension = pr1

  south-htpy-function-out-of-suspension :
    htpy-function-out-of-suspension →
    f south-suspension ＝ g south-suspension
  south-htpy-function-out-of-suspension = pr1 ∘ pr2

  meridian-htpy-function-out-of-suspension :
    (h : htpy-function-out-of-suspension) →
    (x : X) →
    coherence-square-identifications
      ( north-htpy-function-out-of-suspension h)
      ( ap f (meridian-suspension x))
      ( ap g (meridian-suspension x))
      ( south-htpy-function-out-of-suspension h)
  meridian-htpy-function-out-of-suspension = pr2 ∘ pr2

  equiv-htpy-function-out-of-suspension-dependent-suspension-structure :
    ( dependent-suspension-structure
      ( eq-value f g)
      ( suspension-structure-suspension X)) ≃
    ( htpy-function-out-of-suspension)
  equiv-htpy-function-out-of-suspension-dependent-suspension-structure =
    ( equiv-tot
      ( λ p →
        equiv-tot
          ( λ q →
            equiv-Π-equiv-family
              ( λ x →
                inv-equiv
                  ( compute-dependent-identification-eq-value-function
                    ( f)
                    ( g)
                    ( meridian-suspension-structure
                      ( suspension-structure-suspension X)
                      ( x))
                    ( p)
                    ( q))))))

  equiv-dependent-suspension-structure-htpy-function-out-of-suspension :
    ( htpy-function-out-of-suspension) ≃
    ( dependent-suspension-structure
      ( eq-value f g)
      ( suspension-structure-suspension X))
  equiv-dependent-suspension-structure-htpy-function-out-of-suspension =
    ( equiv-tot
      ( λ p →
        equiv-tot
          ( λ q →
            equiv-Π-equiv-family
              ( λ x →
                ( compute-dependent-identification-eq-value-function
                  ( f)
                  ( g)
                  ( meridian-suspension-structure
                    ( suspension-structure-suspension X)
                    ( x))
                  ( p)
                  ( q))))))

  compute-inv-equiv-htpy-function-out-of-suspension-dependent-suspension-structure :
    htpy-equiv
      ( inv-equiv
        ( equiv-htpy-function-out-of-suspension-dependent-suspension-structure))
      ( equiv-dependent-suspension-structure-htpy-function-out-of-suspension)
  compute-inv-equiv-htpy-function-out-of-suspension-dependent-suspension-structure =
    ( compute-inv-equiv-tot
      ( λ p →
        equiv-tot
          ( λ q →
            equiv-Π-equiv-family
              ( λ x →
                inv-equiv
                  ( compute-dependent-identification-eq-value-function
                    ( f)
                    ( g)
                    ( meridian-suspension-structure
                      ( suspension-structure-suspension X)
                      ( x))
                    ( p)
                    ( q)))))) ∙h
    ( tot-htpy
      ( λ p →
        compute-inv-equiv-tot
          ( λ q →
            equiv-Π-equiv-family
              ( λ x →
                inv-equiv
                  ( compute-dependent-identification-eq-value-function
                    ( f)
                    ( g)
                    ( meridian-suspension-structure
                      ( suspension-structure-suspension X)
                      ( x))
                    ( p)
                    ( q)))))) ∙h
    ( tot-htpy
      ( λ p →
        ( tot-htpy
          ( λ q →
            compute-inv-equiv-Π-equiv-family
              ( λ x →
                inv-equiv
                  ( compute-dependent-identification-eq-value-function
                    ( f)
                    ( g)
                    ( meridian-suspension-structure
                      ( suspension-structure-suspension X)
                      ( x))
                    ( p)
                    ( q)))))))

  equiv-htpy-function-out-of-suspension-htpy :
    (f ~ g) ≃ htpy-function-out-of-suspension
  equiv-htpy-function-out-of-suspension-htpy =
    ( equiv-htpy-function-out-of-suspension-dependent-suspension-structure) ∘e
    ( equiv-dependent-up-suspension (eq-value f g))

  htpy-function-out-of-suspension-htpy :
    (f ~ g) → htpy-function-out-of-suspension
  htpy-function-out-of-suspension-htpy =
    map-equiv (equiv-htpy-function-out-of-suspension-htpy)

  equiv-htpy-htpy-function-out-of-suspension :
    htpy-function-out-of-suspension ≃ (f ~ g)
  equiv-htpy-htpy-function-out-of-suspension =
    ( inv-equiv (equiv-dependent-up-suspension (eq-value f g))) ∘e
    ( equiv-dependent-suspension-structure-htpy-function-out-of-suspension)

  htpy-htpy-function-out-of-suspension :
    htpy-function-out-of-suspension → (f ~ g)
  htpy-htpy-function-out-of-suspension =
    map-equiv equiv-htpy-htpy-function-out-of-suspension

  compute-inv-equiv-htpy-function-out-of-suspension-htpy :
    htpy-equiv
      ( inv-equiv equiv-htpy-function-out-of-suspension-htpy)
      ( equiv-htpy-htpy-function-out-of-suspension)
  compute-inv-equiv-htpy-function-out-of-suspension-htpy c =
    ( htpy-eq-equiv
      ( distributive-inv-comp-equiv
        ( equiv-dependent-up-suspension (eq-value f g))
        ( equiv-htpy-function-out-of-suspension-dependent-suspension-structure))
      ( c)) ∙
    ( ap
      ( map-inv-equiv (equiv-dependent-up-suspension (eq-value-function f g)))
      ( compute-inv-equiv-htpy-function-out-of-suspension-dependent-suspension-structure
        ( c)))

  is-section-htpy-htpy-function-out-of-suspension :
    ( ( htpy-function-out-of-suspension-htpy) ∘
    ( htpy-htpy-function-out-of-suspension)) ~
    ( id)
  is-section-htpy-htpy-function-out-of-suspension c =
    ( ap
      ( htpy-function-out-of-suspension-htpy)
      ( inv (compute-inv-equiv-htpy-function-out-of-suspension-htpy c))) ∙
    ( is-section-map-inv-equiv (equiv-htpy-function-out-of-suspension-htpy) c)

  equiv-htpy-function-out-of-suspension-htpy-north-suspension :
    (c : htpy-function-out-of-suspension) →
      ( htpy-htpy-function-out-of-suspension c north-suspension) ＝
      ( north-htpy-function-out-of-suspension c)
  equiv-htpy-function-out-of-suspension-htpy-north-suspension c =
    north-htpy-in-htpy-suspension-structure
      ( htpy-eq-htpy-suspension-structure
        ( is-section-htpy-htpy-function-out-of-suspension c))

  equiv-htpy-function-out-of-suspension-htpy-south-suspension :
    (c : htpy-function-out-of-suspension) →
      ( htpy-htpy-function-out-of-suspension c south-suspension) ＝
      ( south-htpy-function-out-of-suspension c)
  equiv-htpy-function-out-of-suspension-htpy-south-suspension c =
    south-htpy-in-htpy-suspension-structure
      ( htpy-eq-htpy-suspension-structure
        ( is-section-htpy-htpy-function-out-of-suspension c))
```

### The suspension of a contractible type is contractible

```agda
is-contr-suspension-is-contr :
  {l : Level} {X : UU l} → is-contr X → is-contr (suspension X)
is-contr-suspension-is-contr {l} {X} is-contr-X =
  is-contr-is-equiv'
    ( unit)
    ( pr1 (pr2 (cocone-pushout terminal-map terminal-map)))
    ( is-equiv-universal-property-pushout
      ( terminal-map)
      ( terminal-map)
      ( cocone-pushout
        ( terminal-map)
        ( terminal-map))
      ( is-equiv-is-contr terminal-map is-contr-X is-contr-unit)
      ( up-pushout terminal-map terminal-map))
    ( is-contr-unit)
```

### Suspensions increase connectedness

More precisely, the suspension of a `k`-connected type is `(k+1)`-connected.

For the proof we use that a type `A` is `n`-connected if and only if the
constant map `B → (A → B)` is an equivalence for all `n`-types `B`.

So for any `(k+1)`-type `Y`, we have the commutative diagram

```text
                 const
     Y ---------------------->  (suspension X → Y)
     ^                                  |
 pr1 | ≃                              ≃ | ev-suspension
     |                      ≃           v
  Σ (y y' : Y) , y ＝ y' <----- suspension-structure Y
                                ≐ Σ (y y' : Y) , X → y ＝ y'
```

where the bottom map is induced by the equivalence `(y ＝ y') → (X → (y ＝ y'))`
given by the fact that `X` is `k`-connected and `y ＝ y'` is a `k`-type.

Since the left, bottom and right maps are equivalences, so is the top map, as
desired.

```agda
module _
  {l : Level} {k : 𝕋} {X : UU l}
  where

  is-equiv-north-suspension-ev-suspension-is-connected-Truncated-Type :
    is-connected k X →
    {l' : Level} (Y : Truncated-Type l' (succ-𝕋 k)) →
    is-equiv
      ( ( north-suspension-structure) ∘
        ( ev-suspension
          ( suspension-structure-suspension X)
          ( type-Truncated-Type Y)))
  is-equiv-north-suspension-ev-suspension-is-connected-Truncated-Type c Y =
    is-equiv-comp
      ( north-suspension-structure)
      ( ev-suspension
        ( suspension-structure-suspension X)
        ( type-Truncated-Type Y))
      ( is-equiv-ev-suspension
        ( suspension-structure-suspension X)
        ( up-pushout terminal-map terminal-map) (type-Truncated-Type Y))
      ( is-equiv-pr1-is-contr
        ( λ y →
          is-torsorial-fiber-Id
            ( λ y' →
              ( const X (y ＝ y') ,
                is-equiv-diagonal-is-connected (Id-Truncated-Type Y y y') c))))

  is-connected-succ-suspension-is-connected :
    is-connected k X → is-connected (succ-𝕋 k) (suspension X)
  is-connected-succ-suspension-is-connected c =
    is-connected-is-equiv-diagonal
      ( λ Y →
        is-equiv-right-factor
          ( ( north-suspension-structure) ∘
            ( ev-suspension
              ( suspension-structure-suspension X)
              ( type-Truncated-Type Y)))
          ( const (suspension X) (type-Truncated-Type Y))
          ( is-equiv-north-suspension-ev-suspension-is-connected-Truncated-Type
              ( c)
              ( Y))
          ( is-equiv-id))
```
