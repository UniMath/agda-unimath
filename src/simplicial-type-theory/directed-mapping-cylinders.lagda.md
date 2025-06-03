# Directed mapping cylinders

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.directed-mapping-cylinders
  {lI : Level} (I : Nontrivial-Bounded-Total-Order lI lI)
  where
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

open import simplicial-type-theory.arrows I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval-type I
open import simplicial-type-theory.inequality-directed-interval-type I

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

Given a map `f : X → Y`, we define the {{#concept "directed mapping cylinder"}}
of `f` as the [pushout](synthetic-homotopy-theory.pushouts.md)

```text
                  f
            X --------> Y
            |           |
  (id , 1▵) |           |
            ∨         ⌜ ∨
          X × Δ¹ ----> cyl₂ f
```

Intuitively, the directed mapping cylinder of `f` can be understood as `X` glued
to `Y` along `f` by [directed edges](simplicial-type-theory.directed-edges.md)
`x →▵ f x` for every `x : X`.

## Definitions

### The standard directed mapping cylinder of a function

```agda
directed-mapping-cylinder :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (X → Y) → UU (lI ⊔ l1 ⊔ l2)
directed-mapping-cylinder {X = X} {Y} f =
  pushout (λ (x : X) → (x , 1▵)) f

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  in-domain-interval-directed-mapping-cylinder :
    X → Δ¹ → directed-mapping-cylinder f
  in-domain-interval-directed-mapping-cylinder x t =
    inl-pushout (λ (x : X) → (x , 1▵)) f (x , t)

  in-domain-directed-mapping-cylinder : X → directed-mapping-cylinder f
  in-domain-directed-mapping-cylinder x =
    in-domain-interval-directed-mapping-cylinder x 0▵

  in-codomain-directed-mapping-cylinder : Y → directed-mapping-cylinder f
  in-codomain-directed-mapping-cylinder =
    inr-pushout (λ (x : X) → (x , 1▵)) f

  glue-directed-mapping-cylinder :
    (x : X) →
    in-domain-interval-directed-mapping-cylinder x 1▵ ＝
    in-codomain-directed-mapping-cylinder (f x)
  glue-directed-mapping-cylinder =
    glue-pushout (λ (x : X) → (x , 1▵)) f

  hom-directed-mapping-cylinder :
    (x : X) →
    in-domain-directed-mapping-cylinder x →▵
    in-codomain-directed-mapping-cylinder (f x)
  hom-directed-mapping-cylinder x =
    ( in-domain-interval-directed-mapping-cylinder x ,
      refl ,
      glue-directed-mapping-cylinder x)

  cocone-directed-mapping-cylinder :
    cocone (λ (x : X) → (x , 1▵)) f (directed-mapping-cylinder f)
  cocone-directed-mapping-cylinder =
    cocone-pushout (λ (x : X) → (x , 1▵)) f
```

### The dependent cogap map for the directed mapping cylinder

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  dependent-cogap-directed-mapping-cylinder' :
    {l : Level} {P : directed-mapping-cylinder f → UU l}
    (c :
      dependent-cocone (λ x → (x , 1▵)) (f)
        ( cocone-directed-mapping-cylinder f)
        ( P))
    (x : directed-mapping-cylinder f) → P x
  dependent-cogap-directed-mapping-cylinder' =
    dependent-cogap (λ x → (x , 1▵)) f

  dependent-cogap-directed-mapping-cylinder :
    { l : Level} {P : directed-mapping-cylinder f → UU l}
    ( g :
      (x : X) (t : Δ¹) →
      P (in-domain-interval-directed-mapping-cylinder f x t)) →
    ( h : (y : Y) → P (in-codomain-directed-mapping-cylinder f y)) →
    ( p :
      (x : X) →
      dependent-identification P
        ( glue-directed-mapping-cylinder f x)
        ( g x 1▵)
        ( h (f x)))
    ( x : directed-mapping-cylinder f) → P x
  dependent-cogap-directed-mapping-cylinder g h p =
    dependent-cogap-directed-mapping-cylinder'
      ( (λ (x , t) → g x t) , h , p)
```

### The cogap map for the directed mapping cylinder

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} {S : UU l3}
  where

  cogap-directed-mapping-cylinder' :
    cocone (λ x → (x , 1▵)) f S →
    directed-mapping-cylinder f → S
  cogap-directed-mapping-cylinder' =
    cogap (λ (x : X) → (x , 1▵)) f

  cogap-directed-mapping-cylinder :
    (g : X → Δ¹ → S) (h : Y → S) (p : (x : X) → g x 1▵ ＝ h (f x)) →
    directed-mapping-cylinder f → S
  cogap-directed-mapping-cylinder g h p =
    cogap-directed-mapping-cylinder' ((λ (x , t) → g x t) , h , p)

  compute-in-codomain-cogap-directed-mapping-cylinder :
    (g : X → Δ¹ → S) (h : Y → S) (p : (x : X) → g x 1▵ ＝ h (f x)) →
    (y : Y) →
    cogap-directed-mapping-cylinder g h p
      ( in-codomain-directed-mapping-cylinder f y) ＝
    ( h y)
  compute-in-codomain-cogap-directed-mapping-cylinder g h p =
    compute-inr-cogap (λ x → (x , 1▵)) f ((λ (x , t) → g x t) , h , p)

  compute-in-domain-interval-cogap-directed-mapping-cylinder :
    (g : X → Δ¹ → S) (h : Y → S) (p : (x : X) → g x 1▵ ＝ h (f x))
    (x : X) (t : Δ¹) →
    cogap-directed-mapping-cylinder g h p
      ( in-domain-interval-directed-mapping-cylinder f x t) ＝
    ( g x t)
  compute-in-domain-interval-cogap-directed-mapping-cylinder g h p x t =
    compute-inl-cogap
      ( λ x → (x , 1▵))
      ( f)
      ( (λ (x , t) → g x t) , h , p)
      ( x , t)

  compute-in-domain-cogap-directed-mapping-cylinder :
    (g : X → Δ¹ → S) (h : Y → S) (p : (x : X) → g x 1▵ ＝ h (f x)) (x : X) →
    cogap-directed-mapping-cylinder g h p
      ( in-domain-directed-mapping-cylinder f x) ＝
    g x 0▵
  compute-in-domain-cogap-directed-mapping-cylinder g h p x =
    compute-in-domain-interval-cogap-directed-mapping-cylinder g h p x 0▵
```
