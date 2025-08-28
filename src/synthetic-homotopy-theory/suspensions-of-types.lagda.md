# Suspensions of types

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module synthetic-homotopy-theory.suspensions-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.0-connected-types
open import foundation.inhabited-types
open import foundation.booleans
open import foundation.commuting-squares-of-identifications
open import foundation.connected-types
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.set-truncations
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.surjective-maps
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-spans
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

The {{#concept "suspension" WD="suspension" WDID=Q1307987 Agda=suspension}} of a
type `X` is the [pushout](synthetic-homotopy-theory.pushouts.md) of the
[span](foundation.spans.md)

```text
  1 <--- X ---> 1
```

Suspensions play an important role in synthetic homotopy theory. For example,
they star in the freudenthal suspension theorem and give us a definition of
[the spheres](synthetic-homotopy-theory.spheres.md).

## Definitions

### The suspension of a type

```agda
suspension :
  {l : Level} → UU l → UU l
suspension X = pushout (terminal-map X) (terminal-map X)

north-suspension :
  {l : Level} {X : UU l} → suspension X
north-suspension {X = X} =
  inl-pushout (terminal-map X) (terminal-map X) star

south-suspension :
  {l : Level} {X : UU l} → suspension X
south-suspension {X = X} =
  inr-pushout (terminal-map X) (terminal-map X) star

meridian-suspension :
  {l : Level} {X : UU l} → X →
  north-suspension {X = X} ＝ south-suspension {X = X}
meridian-suspension {X = X} =
  glue-pushout (terminal-map X) (terminal-map X)

suspension-structure-suspension :
  {l : Level} (X : UU l) → suspension-structure X (suspension X)
pr1 (suspension-structure-suspension X) = north-suspension
pr1 (pr2 (suspension-structure-suspension X)) = south-suspension
pr2 (pr2 (suspension-structure-suspension X)) = meridian-suspension

cocone-suspension :
  {l : Level} (X : UU l) →
  cocone (terminal-map X) (terminal-map X) (suspension X)
cocone-suspension X =
  cocone-pushout (terminal-map X) (terminal-map X)

cogap-suspension' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  cocone (terminal-map X) (terminal-map X) Y → suspension X → Y
cogap-suspension' {X = X} = cogap (terminal-map X) (terminal-map X)

up-suspension' :
  {l1 : Level} (X : UU l1) →
  universal-property-pushout
    ( terminal-map X)
    ( terminal-map X)
    ( cocone-suspension X)
up-suspension' X = up-pushout (terminal-map X) (terminal-map X)
```

### The cogap map of a suspension structure

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (s : suspension-structure X Y)
  where

  cogap-suspension : suspension X → Y
  cogap-suspension =
    cogap-suspension' (suspension-cocone-suspension-structure s)
```

### The property of being a suspension

The [proposition](foundation-core.propositions.md) `is-suspension` is the
assertion that the cogap map is an
[equivalence](foundation-core.equivalences.md). Note that this proposition is
[small](foundation-core.small-types.md), whereas
[the universal property](foundation-core.universal-property-pullbacks.md) is a
large proposition.

```agda
is-suspension :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  suspension-structure X Y → UU (l1 ⊔ l2)
is-suspension s = is-equiv (cogap-suspension s)
```

## Properties

### The suspension of `X` has the universal property of suspensions

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2}
  where

  is-section-cogap-suspension :
    is-section
      ( ev-suspension (suspension-structure-suspension X) Z)
      ( cogap-suspension)
  is-section-cogap-suspension =
    ( suspension-structure-suspension-cocone) ·l
    ( is-section-cogap (terminal-map X) (terminal-map X)) ·r
    ( suspension-cocone-suspension-structure)

  is-retraction-cogap-suspension :
    is-retraction
      ( ev-suspension (suspension-structure-suspension X) Z)
      ( cogap-suspension)
  is-retraction-cogap-suspension =
    ( is-retraction-cogap (terminal-map X) (terminal-map X))

up-suspension :
  {l1 : Level} {X : UU l1} →
  universal-property-suspension (suspension-structure-suspension X)
up-suspension Z =
  is-equiv-is-invertible
    ( cogap-suspension)
    ( is-section-cogap-suspension)
    ( is-retraction-cogap-suspension)

module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2}
  where

  equiv-up-suspension :
    (suspension X → Z) ≃ (suspension-structure X Z)
  pr1 equiv-up-suspension =
    ev-suspension (suspension-structure-suspension X) Z
  pr2 equiv-up-suspension = up-suspension Z

  compute-north-cogap-suspension :
    (c : suspension-structure X Z) →
    ( cogap-suspension c north-suspension) ＝
    ( north-suspension-structure c)
  compute-north-cogap-suspension c =
    pr1
      ( htpy-eq-suspension-structure
        ( is-section-cogap-suspension c))

  compute-south-cogap-suspension :
    (c : suspension-structure X Z) →
    ( cogap-suspension c south-suspension) ＝
    ( south-suspension-structure c)
  compute-south-cogap-suspension c =
    pr1
      ( pr2
        ( htpy-eq-suspension-structure
          ( is-section-cogap-suspension c)))

  compute-meridian-cogap-suspension :
    (c : suspension-structure X Z) (x : X) →
    ( ( ap (cogap-suspension c) (meridian-suspension x)) ∙
      ( compute-south-cogap-suspension c)) ＝
    ( ( compute-north-cogap-suspension c) ∙
      ( meridian-suspension-structure c x))
  compute-meridian-cogap-suspension c =
    pr2
      ( pr2
        ( htpy-eq-suspension-structure
          ( is-section-cogap-suspension c)))

  ev-suspension-up-suspension :
    (c : suspension-structure X Z) →
    ( ev-suspension
      ( suspension-structure-suspension X)
      ( Z)
      ( cogap-suspension c)) ＝ c
  ev-suspension-up-suspension c =
    eq-htpy-suspension-structure
      ( ( compute-north-cogap-suspension c) ,
        ( compute-south-cogap-suspension c) ,
        ( compute-meridian-cogap-suspension c))
```

### The suspension of `X` has the dependent universal property of suspensions

```agda
dup-suspension :
  {l1 : Level} {X : UU l1} →
  dependent-universal-property-suspension (suspension-structure-suspension X)
dup-suspension {X = X} B =
  is-equiv-htpy-equiv'
    ( ( equiv-dependent-suspension-structure-suspension-cocone
        ( suspension-structure-suspension X)
        ( B)) ∘e
      ( equiv-dup-pushout (terminal-map X) (terminal-map X) B))
    ( triangle-dependent-ev-suspension (suspension-structure-suspension X) B)

equiv-dup-suspension :
  {l1 l2 : Level} {X : UU l1} (B : suspension X → UU l2) →
  ( (x : suspension X) → B x) ≃
  ( dependent-suspension-structure B (suspension-structure-suspension X))
pr1 (equiv-dup-suspension {X = X} B) =
  dependent-ev-suspension (suspension-structure-suspension X) B
pr2 (equiv-dup-suspension B) = dup-suspension B

module _
  {l1 l2 : Level} {X : UU l1} (B : suspension X → UU l2)
  where

  dependent-cogap-suspension :
    dependent-suspension-structure B (suspension-structure-suspension X) →
    (x : suspension X) → B x
  dependent-cogap-suspension = map-inv-is-equiv (dup-suspension B)

  is-section-dependent-cogap-suspension :
    ( ( dependent-ev-suspension (suspension-structure-suspension X) B) ∘
      ( dependent-cogap-suspension)) ~ id
  is-section-dependent-cogap-suspension =
    is-section-map-inv-is-equiv (dup-suspension B)

  is-retraction-dependent-cogap-suspension :
    ( ( dependent-cogap-suspension) ∘
      ( dependent-ev-suspension (suspension-structure-suspension X) B)) ~ id
  is-retraction-dependent-cogap-suspension =
    is-retraction-map-inv-is-equiv (dup-suspension B)

  dup-suspension-north-suspension :
    (d :
      dependent-suspension-structure
        ( B)
        ( suspension-structure-suspension X)) →
    ( dependent-cogap-suspension d north-suspension) ＝
    ( north-dependent-suspension-structure d)
  dup-suspension-north-suspension d =
    north-htpy-dependent-suspension-structure
      ( B)
      ( htpy-eq-dependent-suspension-structure
        ( B)
        ( is-section-dependent-cogap-suspension d))

  dup-suspension-south-suspension :
    (d :
      dependent-suspension-structure
        ( B)
        ( suspension-structure-suspension X)) →
    ( dependent-cogap-suspension d south-suspension) ＝
    ( south-dependent-suspension-structure d)
  dup-suspension-south-suspension d =
    south-htpy-dependent-suspension-structure
      ( B)
      ( htpy-eq-dependent-suspension-structure
        ( B)
        ( is-section-dependent-cogap-suspension d))

  dup-suspension-meridian-suspension :
    (d :
      dependent-suspension-structure
        ( B)
        ( suspension-structure-suspension X))
    (x : X) →
    coherence-square-identifications
      ( ap
        ( tr B (meridian-suspension x))
        ( dup-suspension-north-suspension d))
      ( apd
        ( dependent-cogap-suspension d)
        ( meridian-suspension x))
      ( meridian-dependent-suspension-structure d x)
      ( dup-suspension-south-suspension d)
  dup-suspension-meridian-suspension d =
    meridian-htpy-dependent-suspension-structure
      ( B)
      ( htpy-eq-dependent-suspension-structure
        ( B)
        ( is-section-dependent-cogap-suspension d))
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
        ( compute-inv-equiv-tot
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
                    ( q))))) ∙h
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
    ( equiv-dup-suspension (eq-value f g))

  htpy-function-out-of-suspension-htpy :
    (f ~ g) → htpy-function-out-of-suspension
  htpy-function-out-of-suspension-htpy =
    map-equiv (equiv-htpy-function-out-of-suspension-htpy)

  equiv-htpy-htpy-function-out-of-suspension :
    htpy-function-out-of-suspension ≃ (f ~ g)
  equiv-htpy-htpy-function-out-of-suspension =
    ( inv-equiv (equiv-dup-suspension (eq-value f g))) ∘e
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
        ( equiv-dup-suspension (eq-value f g))
        ( equiv-htpy-function-out-of-suspension-dependent-suspension-structure))
      ( c)) ∙
    ( ap
      ( map-inv-equiv (equiv-dup-suspension (eq-value-function f g)))
      ( compute-inv-equiv-htpy-function-out-of-suspension-dependent-suspension-structure
        ( c)))

  is-section-htpy-htpy-function-out-of-suspension :
    is-section
      htpy-function-out-of-suspension-htpy
      htpy-htpy-function-out-of-suspension
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

### The booleans surject onto suspensions

```agda
module _
  {l : Level} {X : UU l}
  where

  map-surjection-bool-suspension : bool → suspension X
  map-surjection-bool-suspension true = north-suspension
  map-surjection-bool-suspension false = south-suspension

  is-surjective-map-surjection-bool-suspension :
    is-surjective map-surjection-bool-suspension
  is-surjective-map-surjection-bool-suspension =
    dependent-cogap-suspension
      ( λ x → ║ fiber map-surjection-bool-suspension x ║₋₁)
      ( unit-trunc-Prop (true , refl) ,
        unit-trunc-Prop (false , refl) ,
        ( λ _ →
          eq-type-Prop
            ( trunc-Prop
              ( fiber
                ( map-surjection-bool-suspension)
                ( south-suspension)))))

  surjection-bool-suspension : bool ↠ suspension X
  surjection-bool-suspension =
    map-surjection-bool-suspension ,
    is-surjective-map-surjection-bool-suspension
```

### The suspension of a contractible type is contractible

```agda
abstract
  is-contr-suspension-is-contr :
    {l : Level} {X : UU l} → is-contr X → is-contr (suspension X)
  is-contr-suspension-is-contr {X = X} is-contr-X =
    is-contr-is-equiv'
      ( unit)
      ( pr1 (pr2 (cocone-suspension X)))
      ( is-equiv-universal-property-pushout
        ( terminal-map X)
        ( terminal-map X)
        ( cocone-suspension X)
        ( is-equiv-is-contr (terminal-map X) is-contr-X is-contr-unit)
        ( up-suspension' X))
      ( is-contr-unit)
```

### Suspensions increase connectedness

More precisely, the suspension of a `k`-connected type is `(k+1)`-connected.

For the proof we use that a type `A` is `n`-connected if and only if the
constant map `B → (A → B)` is an equivalence for all `n`-types `B`.

So for any `(k+1)`-type `Y`, we have the commutative diagram

```text
                 Δ
     Y ---------------------->  (suspension X → Y)
     ∧                                  |
 pr1 | ≃                              ≃ | ev-suspension
     |                      ≃           ∨
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
        ( up-suspension' X)
        ( type-Truncated-Type Y))
      ( is-equiv-pr1-is-contr
        ( λ y →
          is-torsorial-fiber-Id
            ( λ y' →
              ( diagonal-exponential (y ＝ y') X ,
                is-equiv-diagonal-exponential-is-connected
                  ( Id-Truncated-Type Y y y')
                  ( c)))))

  is-connected-succ-suspension-is-connected :
    is-connected k X → is-connected (succ-𝕋 k) (suspension X)
  is-connected-succ-suspension-is-connected c =
    is-connected-is-equiv-diagonal-exponential
      ( λ Y →
        is-equiv-right-factor
          ( ( north-suspension-structure) ∘
            ( ev-suspension
              ( suspension-structure-suspension X)
              ( type-Truncated-Type Y)))
          ( diagonal-exponential (type-Truncated-Type Y) (suspension X))
          ( is-equiv-north-suspension-ev-suspension-is-connected-Truncated-Type
              ( c)
              ( Y))
          ( is-equiv-id))
```

### `Σ X` is 0-connected if and only if `X` is inhabited

Note that `Σ empty = bool` is not 0-connected.

The forward direction is the subtle one. When `Σ X` is 0-connected, then in
particular we merely have `p ∈ north-suspension ＝ south-suspension`; such
identifications are generated by `X`.

```agda
suspension-is-0-connected-is-inhabited :
  {l : Level} (X : UU l) → is-inhabited X → is-0-connected (suspension X)
suspension-is-0-connected-is-inhabited X x =
  is-connected-succ-suspension-is-connected
    ( is-neg-one-connected-is-inhabited X x)

is-inhabited-suspension-is-0-connected :
  {l : Level} (X : UU l) → is-0-connected (suspension X) → is-inhabited X
is-inhabited-suspension-is-0-connected X (sx , p) =
  {!   !}
```
