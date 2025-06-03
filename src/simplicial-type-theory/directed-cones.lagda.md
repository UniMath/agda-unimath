# The directed cone

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.directed-cones
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
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

Given a type `X`, we define the {{#concept "directed cone type"}} as the
[pushout](synthetic-homotopy-theory.pushouts.md)

```text
            X --------> 1
            |           |
  (id , 0▵) |           |
            ∨         ⌜ ∨
          X × Δ¹ ---> directed-cone X
```

Intuitively, the directed cone of `X` can be understood as `X` with a point `*`
attached such that there is a
[directed edge](simplicial-type-theory.directed-edges.md) `* →▵ x` for every
`x : X`.

## Definitions

### The standard directed cone on a type

```agda
directed-cone : {l : Level} → UU l → UU (I1 ⊔ l)
directed-cone X =
  pushout (λ (x : X) → (x , 0▵)) (terminal-map X)

module _
  {l : Level} {X : UU l}
  where

  in-directed-cone' : X → Δ¹ → directed-cone X
  in-directed-cone' x t =
    inl-pushout (λ (x : X) → (x , 0▵)) (terminal-map X) (x , t)

  in-directed-cone : X → directed-cone X
  in-directed-cone x = in-directed-cone' x 1▵

  point-directed-cone : directed-cone X
  point-directed-cone =
    inr-pushout (λ (x : X) → (x , 0▵)) (terminal-map X) star

  glue-directed-cone :
    (x : X) →
    in-directed-cone' x 0▵ ＝ point-directed-cone
  glue-directed-cone =
    glue-pushout (λ (x : X) → (x , 0▵)) (terminal-map X)

  hom-directed-cone :
    (x : X) → point-directed-cone →▵ in-directed-cone x
  hom-directed-cone x =
    ( in-directed-cone' x , glue-directed-cone x , refl)

  cocone-directed-cone :
    cocone (λ (x : X) → (x , 0▵)) (terminal-map X) (directed-cone X)
  cocone-directed-cone =
    cocone-pushout (λ (x : X) → (x , 0▵)) (terminal-map X)
```

### The dependent cogap map for the directed cone type

```agda
module _
  {l : Level} (X : UU l)
  where

  dependent-cogap-directed-cone' :
    {l' : Level} {P : directed-cone X → UU l'}
    (c :
      dependent-cocone
        ( λ x → x , 0▵)
        ( terminal-map X)
        ( cocone-directed-cone)
        ( P))
    (x : directed-cone X) → P x
  dependent-cogap-directed-cone' =
    dependent-cogap (λ x → (x , 0▵)) (terminal-map X)

  dependent-cogap-directed-cone :
    { l' : Level} {P : directed-cone X → UU l'}
    ( f : P point-directed-cone) →
    ( g : (x : X) (t : Δ¹) → P (in-directed-cone' x t)) →
    ( p :
      (x : X) →
      dependent-identification P (glue-directed-cone x) (g x 0▵) f)
    ( x : directed-cone X) → P x
  dependent-cogap-directed-cone f g p =
    dependent-cogap-directed-cone'
      ( (λ (x , t) → g x t) , point f , p)
```

### The cogap map for the directed cone type

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  cogap-directed-cone' :
    cocone (λ x → (x , 0▵)) (terminal-map X) Y →
    directed-cone X → Y
  cogap-directed-cone' =
    cogap (λ (x : X) → (x , 0▵)) (terminal-map X)

  cogap-directed-cone :
    (g : X → Δ¹ → Y) (f : Y) (p : (x : X) → g x 0▵ ＝ f) →
    directed-cone X → Y
  cogap-directed-cone g f p =
    cogap-directed-cone' ((λ (x , t) → g x t) , point f , p)

  compute-point-cogap-directed-cone :
    (g : X → Δ¹ → Y) (f : Y) (p : (x : X) → g x 0▵ ＝ f) →
    cogap-directed-cone g f p point-directed-cone ＝ f
  compute-point-cogap-directed-cone g f p =
    compute-inr-cogap
      ( λ x → (x , 0▵))
      ( terminal-map X)
      ( (λ (x , t) → g x t) , point f , p)
      ( star)

  compute-in-cogap-directed-cone' :
    (g : X → Δ¹ → Y) (f : Y) (p : (x : X) → g x 0▵ ＝ f) (x : X) (t : Δ¹) →
    cogap-directed-cone g f p (in-directed-cone' x t) ＝
    g x t
  compute-in-cogap-directed-cone' g f p x t =
    compute-inl-cogap
      ( λ x → x , 0▵)
      ( terminal-map X)
      ( (λ (x , t) → g x t) , point f , p)
      ( x , t)

  compute-in-cogap-directed-cone :
    (g : X → Δ¹ → Y) (f : Y) (p : (x : X) → g x 0▵ ＝ f) (x : X) →
    cogap-directed-cone g f p (in-directed-cone x) ＝
    g x 1▵
  compute-in-cogap-directed-cone g f p x =
    compute-in-cogap-directed-cone' g f p x 1▵
```

## Properties

### The directed interval is equivalent to the directed cone over the unit type

**Proof.** We have the pushout diagram

```text
  1 -------> 1
  |          |
  |          |
  ∨        ⌜ ∨
  Δ¹ ---> directed-cone 1,
```

and since the top horizontal map is an equivalence, so is its pushout.

This remains to be formalized.
