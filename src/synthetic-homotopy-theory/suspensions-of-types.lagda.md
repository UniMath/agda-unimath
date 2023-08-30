# Suspensions of types

```agda
module synthetic-homotopy-theory.suspensions-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.commuting-squares-of-maps
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-systems
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.transport
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-suspension-structures
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.dependent-universal-property-suspensions
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.universal-property-pushouts
open import synthetic-homotopy-theory.universal-property-suspensions
```

</details>

## Idea

The suspension of a type `X` is the
[pushout](synthetic-homotopy-theory.pushouts.md) of the span

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
suspension X = pushout (const X unit star) (const X unit star)

north-suspension :
  {l : Level} {X : UU l} → suspension X
north-suspension {X = X} =
  inl-pushout (const X unit star) (const X unit star) star

south-suspension :
  {l : Level} {X : UU l} → suspension X
south-suspension {X = X} =
  inr-pushout (const X unit star) (const X unit star) star

meridian-suspension :
  {l : Level} {X : UU l} → X →
  Id (north-suspension {X = X}) (south-suspension {X = X})
meridian-suspension {X = X} =
  glue-pushout (const X unit star) (const X unit star)

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
        ( suspension-structure-suspension X) Z)
      ( is-equiv-map-equiv
        ( ( comparison-suspension-cocone X Z) ∘e
          ( equiv-up-pushout (const X unit star) (const X unit star) Z)))

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
    pr1 (htpy-eq-suspension-structure ((is-section-map-inv-up-suspension Z) c))

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
    ( meridian-suspension-structure c) x)
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
    ( (map-equiv
         (comparison-dependent-suspension-cocone (suspension-structure-suspension X) B)) ∘
      ( dependent-cocone-map
        ( const X unit star)
        ( const X unit star)
        ( cocone-suspension-structure X (suspension X) (suspension-structure-suspension X))
        ( B)))
    ( inv-htpy (triangle-dependent-ev-suspension (suspension-structure-suspension X) B))
    ( is-equiv-comp
      ( map-equiv
        (comparison-dependent-suspension-cocone
          (suspension-structure-suspension X) B))
      ( dependent-cocone-map
        (const X unit star)
        (const X unit star)
        (cocone-suspension-structure X (suspension X)
          (suspension-structure-suspension X))
        ( B))
      ( dependent-up-pushout (const X unit star) (const X unit star) B)
      ( is-equiv-map-equiv
        ( comparison-dependent-suspension-cocone
          ( suspension-structure-suspension X)
          ( B))))

equiv-dependent-up-suspension :
    {l1 l2 : Level} {X : UU l1} (B : (suspension X) → UU l2) →
    ((x : suspension X) → B x) ≃
    ( dependent-suspension-structure B (suspension-structure-suspension X))
pr1 (equiv-dependent-up-suspension {l2 = l2} {X = X} B) =
  (dependent-ev-suspension (suspension-structure-suspension X) B)
pr2 (equiv-dependent-up-suspension {l2 = l2} B) =
  dependent-up-suspension l2 B

module _
  {l1 l2 : Level} {X : UU l1} (B : (suspension X) → UU l2)
  where

  map-inv-dependent-up-suspension :
    dependent-suspension-structure B (suspension-structure-suspension X)  →
    (x : suspension X) → B x
  map-inv-dependent-up-suspension =
    map-inv-is-equiv (dependent-up-suspension l2 B)

  is-section-map-inv-dependent-up-suspension :
    ( ( dependent-ev-suspension (suspension-structure-suspension X) B) ∘
      ( map-inv-dependent-up-suspension)) ~ id
  is-section-map-inv-dependent-up-suspension  =
    is-section-map-inv-is-equiv (dependent-up-suspension l2 B)

  is-retraction-map-inv-dependent-up-suspension :
    ( ( map-inv-dependent-up-suspension) ∘
      ( dependent-ev-suspension (suspension-structure-suspension X) B)) ~ id
  is-retraction-map-inv-dependent-up-suspension =
    is-retraction-map-inv-is-equiv (dependent-up-suspension l2 B)

  dependent-up-suspension-north-suspension :
    (d-susp-str : dependent-suspension-structure B (suspension-structure-suspension X)) →
      ( map-inv-dependent-up-suspension d-susp-str north-suspension) ＝
      ( north-dependent-suspension-structure d-susp-str)
  dependent-up-suspension-north-suspension d-susp-str =
    {!north-htpy-dependent-suspension-structure
    ( B)
    ( htpy-eq-dependent-suspension-structure
      ( B)
      ( is-section-map-inv-dependent-up-suspension d-susp-str))!}

  dependent-up-suspension-south-suspension :
    (d-susp-str : dependent-suspension-structure B (suspension-structure-suspension X)) →
    ( map-inv-dependent-up-suspension d-susp-str south-suspension) ＝
    ( south-dependent-suspension-structure d-susp-str)
  dependent-up-suspension-south-suspension d-susp-str =
    {!S-htpy-dependent-suspension-structure
    ( B)
    ( htpy-eq-dependent-suspension-structure
      ( B)
      ( is-section-map-inv-dependent-up-suspension d-susp-str))!}

  dependent-up-suspension-meridian-suspension :
    (d-susp-str : dependent-suspension-structure
      ( B)
      ( suspension-structure-suspension X))
    (x : X) →
      coherence-square-identifications
        ( apd (map-inv-dependent-up-suspension d-susp-str ) (meridian-suspension x))
        ( dependent-up-suspension-south-suspension d-susp-str)
        ( ap (tr B (meridian-suspension x)) (dependent-up-suspension-north-suspension d-susp-str))
        (meridian-dependent-suspension-structure d-susp-str x)
  dependent-up-suspension-meridian-suspension d-susp-str =
    {!merid-htpy-dependent-suspension-structure
      ( B)
      ( htpy-eq-dependent-suspension-structure
        ( B)
        ( is-section-map-inv-dependent-up-suspension d-susp-str))  !}
```


### The suspension of a contractible type is contractible

```agda
is-contr-suspension-is-contr :
  {l : Level} {X : UU l} → is-contr X → is-contr (suspension X)
is-contr-suspension-is-contr {l} {X} is-contr-X =
  is-contr-is-equiv'
    ( unit)
    ( pr1 (pr2 (cocone-pushout (const X unit star) (const X unit star))))
    ( is-equiv-universal-property-pushout
      ( const X unit star)
      ( const X unit star)
      ( cocone-pushout
        ( const X unit star)
        ( const X unit star))
      ( is-equiv-is-contr (const X unit star) is-contr-X is-contr-unit)
      ( up-pushout (const X unit star) (const X unit star)))
    ( is-contr-unit)
```
