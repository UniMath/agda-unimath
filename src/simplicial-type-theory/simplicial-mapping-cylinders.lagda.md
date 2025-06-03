# Simplicial mapping cylinders

```agda
module simplicial-type-theory.simplicial-mapping-cylinders where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.inequality-directed-interval-type
open import simplicial-type-theory.simplicial-arrows

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

Given a map `f : X → Y`, we define the
{{#concept "simplicial mapping cylinder"}} of `f` as the
[pushout](synthetic-homotopy-theory.pushouts.md)

```text
                  f
            X --------> Y
            |           |
  (id , 1₂) |           |
            ∨         ⌜ ∨
          X × Δ¹ ----> cyl₂ f
```

Intuitively, the simplicial mapping cylinder of `f` can be understood as `X`
simplicially glued to `Y` along `f`. I.e., for every `x : X` there is a
[directed edge](simplicial-type-theory.directed-edges.md) `x →▵ f x`.

## Definitions

### The standard simplicial mapping cylinder of a function

```agda
simplicial-mapping-cylinder :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (X → Y) → UU (l1 ⊔ l2)
simplicial-mapping-cylinder {X = X} {Y} f =
  pushout (λ (x : X) → (x , 1₂)) f

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  in-domain-interval-simplicial-mapping-cylinder :
    X → Δ¹ → simplicial-mapping-cylinder f
  in-domain-interval-simplicial-mapping-cylinder x t =
    inl-pushout (λ (x : X) → (x , 1₂)) f (x , t)

  in-domain-simplicial-mapping-cylinder : X → simplicial-mapping-cylinder f
  in-domain-simplicial-mapping-cylinder x =
    in-domain-interval-simplicial-mapping-cylinder x 0₂

  in-codomain-simplicial-mapping-cylinder : Y → simplicial-mapping-cylinder f
  in-codomain-simplicial-mapping-cylinder =
    inr-pushout (λ (x : X) → (x , 1₂)) f

  glue-simplicial-mapping-cylinder :
    (x : X) →
    in-domain-interval-simplicial-mapping-cylinder x 1₂ ＝
    in-codomain-simplicial-mapping-cylinder (f x)
  glue-simplicial-mapping-cylinder =
    glue-pushout (λ (x : X) → (x , 1₂)) f

  hom-simplicial-mapping-cylinder :
    (x : X) →
    in-domain-simplicial-mapping-cylinder x →▵
    in-codomain-simplicial-mapping-cylinder (f x)
  hom-simplicial-mapping-cylinder x =
    ( in-domain-interval-simplicial-mapping-cylinder x ,
      refl ,
      glue-simplicial-mapping-cylinder x)

  cocone-simplicial-mapping-cylinder :
    cocone (λ (x : X) → (x , 1₂)) f (simplicial-mapping-cylinder f)
  cocone-simplicial-mapping-cylinder =
    cocone-pushout (λ (x : X) → (x , 1₂)) f
```

### The dependent cogap map for the simplicial mapping cylinder

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  dependent-cogap-simplicial-mapping-cylinder' :
    {l : Level} {P : simplicial-mapping-cylinder f → UU l}
    (c :
      dependent-cocone (λ x → (x , 1₂)) (f)
        ( cocone-simplicial-mapping-cylinder f)
        ( P))
    (x : simplicial-mapping-cylinder f) → P x
  dependent-cogap-simplicial-mapping-cylinder' =
    dependent-cogap (λ x → (x , 1₂)) f

  dependent-cogap-simplicial-mapping-cylinder :
    { l : Level} {P : simplicial-mapping-cylinder f → UU l}
    ( g :
      (x : X) (t : Δ¹) →
      P (in-domain-interval-simplicial-mapping-cylinder f x t)) →
    ( h : (y : Y) → P (in-codomain-simplicial-mapping-cylinder f y)) →
    ( p :
      (x : X) →
      dependent-identification P
        ( glue-simplicial-mapping-cylinder f x)
        ( g x 1₂)
        ( h (f x)))
    ( x : simplicial-mapping-cylinder f) → P x
  dependent-cogap-simplicial-mapping-cylinder g h p =
    dependent-cogap-simplicial-mapping-cylinder'
      ( (λ (x , t) → g x t) , h , p)
```

### The cogap map for the simplicial mapping cylinder

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} {S : UU l3}
  where

  cogap-simplicial-mapping-cylinder' :
    cocone (λ x → (x , 1₂)) f S →
    simplicial-mapping-cylinder f → S
  cogap-simplicial-mapping-cylinder' =
    cogap (λ (x : X) → (x , 1₂)) f

  cogap-simplicial-mapping-cylinder :
    (g : X → Δ¹ → S) (h : Y → S) (p : (x : X) → g x 1₂ ＝ h (f x)) →
    simplicial-mapping-cylinder f → S
  cogap-simplicial-mapping-cylinder g h p =
    cogap-simplicial-mapping-cylinder' ((λ (x , t) → g x t) , h , p)

  compute-in-codomain-cogap-simplicial-mapping-cylinder :
    (g : X → Δ¹ → S) (h : Y → S) (p : (x : X) → g x 1₂ ＝ h (f x)) →
    (y : Y) →
    cogap-simplicial-mapping-cylinder g h p
      ( in-codomain-simplicial-mapping-cylinder f y) ＝
    ( h y)
  compute-in-codomain-cogap-simplicial-mapping-cylinder g h p =
    compute-inr-cogap (λ x → (x , 1₂)) f ((λ (x , t) → g x t) , h , p)

  compute-in-domain-interval-cogap-simplicial-mapping-cylinder :
    (g : X → Δ¹ → S) (h : Y → S) (p : (x : X) → g x 1₂ ＝ h (f x))
    (x : X) (t : Δ¹) →
    cogap-simplicial-mapping-cylinder g h p
      ( in-domain-interval-simplicial-mapping-cylinder f x t) ＝
    ( g x t)
  compute-in-domain-interval-cogap-simplicial-mapping-cylinder g h p x t =
    compute-inl-cogap
      ( λ x → (x , 1₂))
      ( f)
      ( (λ (x , t) → g x t) , h , p)
      ( x , t)

  compute-in-domain-cogap-simplicial-mapping-cylinder :
    (g : X → Δ¹ → S) (h : Y → S) (p : (x : X) → g x 1₂ ＝ h (f x)) (x : X) →
    cogap-simplicial-mapping-cylinder g h p
      ( in-domain-simplicial-mapping-cylinder f x) ＝
    g x 0₂
  compute-in-domain-cogap-simplicial-mapping-cylinder g h p x =
    compute-in-domain-interval-cogap-simplicial-mapping-cylinder g h p x 0₂
```
