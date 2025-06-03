# The simplicial cone

```agda
module simplicial-type-theory.simplicial-cones where
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

Given a type `X`, we define the {{#concept "simplicial cone type"}} as the
[pushout](synthetic-homotopy-theory.pushouts.md)

```text
            X --------> 1
            |           |
  (id , 0₂) |           |
            ∨         ⌜ ∨
          X × Δ¹ ---> cone₂ X
```

Intuitively, the simplicial cone of `X` can be understood as `X` with a point
`*` attached such that there is a
[directed edge](simplicial-type-theory.directed-edges.md) `* →▵ x` for every
`x : X`.

## Definitions

### The standard simplicial cone on a type

```agda
simplicial-cone : {l : Level} → UU l → UU l
simplicial-cone X =
  pushout (λ (x : X) → (x , 0₂)) (terminal-map X)

module _
  {l : Level} {X : UU l}
  where

  in-simplicial-cone' : X → Δ¹ → simplicial-cone X
  in-simplicial-cone' x t =
    inl-pushout (λ (x : X) → (x , 0₂)) (terminal-map X) (x , t)

  in-simplicial-cone : X → simplicial-cone X
  in-simplicial-cone x = in-simplicial-cone' x 1₂

  point-simplicial-cone : simplicial-cone X
  point-simplicial-cone =
    inr-pushout (λ (x : X) → (x , 0₂)) (terminal-map X) star

  glue-simplicial-cone :
    (x : X) →
    in-simplicial-cone' x 0₂ ＝ point-simplicial-cone
  glue-simplicial-cone =
    glue-pushout (λ (x : X) → (x , 0₂)) (terminal-map X)

  hom-simplicial-cone :
    (x : X) → point-simplicial-cone →▵ in-simplicial-cone x
  hom-simplicial-cone x =
    ( in-simplicial-cone' x , glue-simplicial-cone x , refl)

  cocone-simplicial-cone :
    cocone (λ (x : X) → (x , 0₂)) (terminal-map X) (simplicial-cone X)
  cocone-simplicial-cone =
    cocone-pushout (λ (x : X) → (x , 0₂)) (terminal-map X)
```

### The dependent cogap map for the simplicial cone type

```agda
module _
  {l : Level} (X : UU l)
  where

  dependent-cogap-simplicial-cone' :
    {l' : Level} {P : simplicial-cone X → UU l'}
    (c :
      dependent-cocone
        ( λ x → x , 0₂)
        ( terminal-map X)
        ( cocone-simplicial-cone)
        ( P))
    (x : simplicial-cone X) → P x
  dependent-cogap-simplicial-cone' =
    dependent-cogap (λ x → (x , 0₂)) (terminal-map X)

  dependent-cogap-simplicial-cone :
    { l' : Level} {P : simplicial-cone X → UU l'}
    ( f : P point-simplicial-cone) →
    ( g : (x : X) (t : Δ¹) → P (in-simplicial-cone' x t)) →
    ( p :
      (x : X) →
      dependent-identification P (glue-simplicial-cone x) (g x 0₂) f)
    ( x : simplicial-cone X) → P x
  dependent-cogap-simplicial-cone f g p =
    dependent-cogap-simplicial-cone'
      ( (λ (x , t) → g x t) , point f , p)
```

### The cogap map for the simplicial cone type

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  cogap-simplicial-cone' :
    cocone (λ x → (x , 0₂)) (terminal-map X) Y →
    simplicial-cone X → Y
  cogap-simplicial-cone' =
    cogap (λ (x : X) → (x , 0₂)) (terminal-map X)

  cogap-simplicial-cone :
    (g : X → Δ¹ → Y) (f : Y) (p : (x : X) → g x 0₂ ＝ f) →
    simplicial-cone X → Y
  cogap-simplicial-cone g f p =
    cogap-simplicial-cone' ((λ (x , t) → g x t) , point f , p)

  compute-point-cogap-simplicial-cone :
    (g : X → Δ¹ → Y) (f : Y) (p : (x : X) → g x 0₂ ＝ f) →
    cogap-simplicial-cone g f p point-simplicial-cone ＝ f
  compute-point-cogap-simplicial-cone g f p =
    compute-inr-cogap
      ( λ x → (x , 0₂))
      ( terminal-map X)
      ( (λ (x , t) → g x t) , point f , p)
      ( star)

  compute-in-cogap-simplicial-cone' :
    (g : X → Δ¹ → Y) (f : Y) (p : (x : X) → g x 0₂ ＝ f) (x : X) (t : Δ¹) →
    cogap-simplicial-cone g f p (in-simplicial-cone' x t) ＝
    g x t
  compute-in-cogap-simplicial-cone' g f p x t =
    compute-inl-cogap
      ( λ x → x , 0₂)
      ( terminal-map X)
      ( (λ (x , t) → g x t) , point f , p)
      ( x , t)

  compute-in-cogap-simplicial-cone :
    (g : X → Δ¹ → Y) (f : Y) (p : (x : X) → g x 0₂ ＝ f) (x : X) →
    cogap-simplicial-cone g f p (in-simplicial-cone x) ＝
    g x 1₂
  compute-in-cogap-simplicial-cone g f p x =
    compute-in-cogap-simplicial-cone' g f p x 1₂
```

## Properties

### The directed interval is equivalent to the simplicial cone over the unit type

**Proof.** We have the pushout diagram

```text
  1 ------> 1
  |         |
  |         |
  ∨       ⌜ ∨
  Δ¹ -----> C₂1,
```

and since the top horizontal map is an equivalence, so is its pushout.

This remains to be formalized.
