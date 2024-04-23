# The universal property of the directed circle

```agda
module simplicial-type-theory.universal-property-directed-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.constant-type-families
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.strictly-right-unital-concatenation-identifications
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import simplicial-type-theory.action-on-simplicial-edges-dependent-functions
open import simplicial-type-theory.action-on-simplicial-edges-functions
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.free-directed-loops
open import simplicial-type-theory.simplicial-arrows
```

</details>

## Definitions

### Evaluating an ordinary function at a free directed loop

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-directed-loop X) (Y : UU l2)
  where

  ev-free-directed-loop : (X → Y) → free-directed-loop Y
  ev-free-directed-loop f =
    ( f ∘ arrow-free-directed-loop α ,
      ap f (compute-target-free-directed-loop α))
```

### The recursion principle of the directed circle

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-directed-loop X)
  where

  recursion-principle-directed-circle : UUω
  recursion-principle-directed-circle =
    {l : Level} (Y : UU l) → section (ev-free-directed-loop α Y)
```

### The universal property of the directed circle

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-directed-loop X)
  where

  universal-property-directed-circle : UUω
  universal-property-directed-circle =
    {l : Level} (Y : UU l) → is-equiv (ev-free-directed-loop α Y)
```

### Evaluating a dependent function at a free directed loop

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-directed-loop X) (P : X → UU l2)
  where

  ev-free-directed-loop-Π : ((x : X) → P x) → free-dependent-directed-loop α P
  ev-free-directed-loop-Π f =
    ( f ∘ arrow-free-directed-loop α ,
      apd f (compute-target-free-directed-loop α))
```

### The induction principle of the directed circle

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-directed-loop X)
  where

  induction-principle-directed-circle : UUω
  induction-principle-directed-circle =
    {l : Level} (P : X → UU l) → section (ev-free-directed-loop-Π α P)

module _
  {l1 l2 : Level} {X : UU l1} (α : free-directed-loop X)
  (H : induction-principle-directed-circle α) (P : X → UU l2)
  (β : free-dependent-directed-loop α P)
  where

  function-induction-principle-directed-circle : (x : X) → P x
  function-induction-principle-directed-circle = pr1 (H P) β

  compute-induction-principle-directed-circle :
    ev-free-directed-loop-Π α P function-induction-principle-directed-circle ＝ β
  compute-induction-principle-directed-circle = pr2 (H P) β
```

### The dependent universal property of the directed circle

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-directed-loop X)
  where

  dependent-universal-property-directed-circle : UUω
  dependent-universal-property-directed-circle =
    {l : Level} (P : X → UU l) → is-equiv (ev-free-directed-loop-Π α P)
```

## Properties

### The induction principle of the directed circle implies the dependent universal property of the directed circle

To prove this, we have to show that the section of `ev-free-directed-loop-Π` is
also a retraction. This construction is also by the induction principle of the
directed circle, but it requires (a minimal amount of) preparations.

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-directed-loop X)
  where

  free-dependent-directed-loop-htpy :
    {l2 : Level} {P : X → UU l2} {f g : (x : X) → P x} →
    ( htpy-free-dependent-directed-loop α P
      ( ev-free-directed-loop-Π α P f)
      ( ev-free-directed-loop-Π α P g)) →
    ( free-dependent-directed-loop α (λ x → f x ＝ g x))
  free-dependent-directed-loop-htpy {l2} {P} {f} {g} (p , q) =
    ( p ,
      map-compute-dependent-identification-eq-value f g
        ( compute-target-free-directed-loop α)
        ( p 1₂)
        ( p 0₂)
        ( equational-reasoning
          apd f (compute-target-free-directed-loop α) ∙ p 0₂
          ＝ apd f (compute-target-free-directed-loop α) ∙ᵣ p 0₂
          by
            eq-right-strict-concat-concat
              ( apd f (compute-target-free-directed-loop α))
              ( p 0₂)
          ＝ concat-dependent-identification P
              ( refl)
              ( compute-target-free-directed-loop α)
              ( p 1₂)
              ( apd g (compute-target-free-directed-loop α))
          by q
          ＝ ap (tr P (compute-target-free-directed-loop α)) (p 1₂) ∙
            apd g (compute-target-free-directed-loop α)
          by
            compute-concat-dependent-identification-left-base-refl P
              ( compute-target-free-directed-loop α)
              ( p 1₂)
              ( apd g (compute-target-free-directed-loop α))))

  is-retraction-ind-directed-circle :
    ( I : induction-principle-directed-circle α)
    { l2 : Level} (P : X → UU l2) →
    is-retraction
      ( ev-free-directed-loop-Π α P)
      ( function-induction-principle-directed-circle α I P)
  is-retraction-ind-directed-circle I P f =
    eq-htpy
      ( function-induction-principle-directed-circle α I
        ( eq-value
          ( function-induction-principle-directed-circle α I P
            ( ev-free-directed-loop-Π α P f))
          ( f))
        ( free-dependent-directed-loop-htpy
          ( htpy-free-dependent-directed-loop-eq α P _ _
            ( compute-induction-principle-directed-circle α I P
              ( ev-free-directed-loop-Π α P f)))))

  abstract
    dependent-universal-property-induction-principle-directed-circle :
      induction-principle-directed-circle α →
      dependent-universal-property-directed-circle α
    dependent-universal-property-induction-principle-directed-circle I P =
      is-equiv-is-invertible
        ( function-induction-principle-directed-circle α I P)
        ( compute-induction-principle-directed-circle α I P)
        ( is-retraction-ind-directed-circle I P)
```

### Uniqueness of the maps obtained from the universal property of the directed circle

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-directed-loop X)
  where

  abstract
    uniqueness-universal-property-directed-circle :
      universal-property-directed-circle α →
      {l2 : Level} (Y : UU l2) (α' : free-directed-loop Y) →
      is-contr
        ( Σ ( X → Y)
            ( λ f → htpy-free-directed-loop (ev-free-directed-loop α Y f) α'))
    uniqueness-universal-property-directed-circle I Y α' =
      is-contr-is-equiv'
        ( fiber (ev-free-directed-loop α Y) α')
        ( tot
          ( λ f → htpy-eq-free-directed-loop (ev-free-directed-loop α Y f) α'))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ f →
            is-equiv-htpy-eq-free-directed-loop
              ( ev-free-directed-loop α Y f)
              ( α')))
        ( is-contr-map-is-equiv (I Y) α')
```

### Uniqueness of the dependent functions obtained from the dependent universal property of the directed circle

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-directed-loop X)
  where

  uniqueness-dependent-universal-property-directed-circle :
    dependent-universal-property-directed-circle α →
    {l2 : Level} {P : X → UU l2} (k : free-dependent-directed-loop α P) →
    is-contr
      ( Σ ( (x : X) → P x)
          ( λ h →
            htpy-free-dependent-directed-loop α P
              ( ev-free-directed-loop-Π α P h)
              ( k)))
  uniqueness-dependent-universal-property-directed-circle I {P = P} k =
    is-contr-is-equiv'
      ( fiber (ev-free-directed-loop-Π α P) k)
      ( tot
        ( λ h →
          htpy-free-dependent-directed-loop-eq α P
            ( ev-free-directed-loop-Π α P h)
            ( k)))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ h →
          is-equiv-htpy-free-dependent-directed-loop-eq α P
            ( ev-free-directed-loop-Π α P h)
            ( k)))
      ( is-contr-map-is-equiv (I P) k)
```

### The dependent universal property of the directed circle implies the universal property of the directed circle

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-directed-loop X) (Y : UU l2)
  where

  triangle-comparison-free-directed-loop :
    map-compute-free-dependent-directed-loop-constant-type-family α Y ∘
    ev-free-directed-loop α Y ~
    ev-free-directed-loop-Π α (λ _ → Y)
  triangle-comparison-free-directed-loop f =
    eq-htpy-free-dependent-directed-loop α
      ( λ _ → Y)
      ( map-compute-free-dependent-directed-loop-constant-type-family α Y
        ( ev-free-directed-loop α Y f))
      ( ev-free-directed-loop-Π α (λ _ → Y) f)
      ( ( refl-htpy) ,
        ( inv
          ( apd-constant-type-family f (compute-target-free-directed-loop α))))

module _
  {l1 : Level} {X : UU l1} (α : free-directed-loop X)
  where

  abstract
    universal-property-dependent-universal-property-directed-circle :
      dependent-universal-property-directed-circle α →
      universal-property-directed-circle α
    universal-property-dependent-universal-property-directed-circle I Y =
      is-equiv-top-map-triangle
        ( ev-free-directed-loop-Π α (λ _ → Y))
        ( map-compute-free-dependent-directed-loop-constant-type-family α Y)
        ( ev-free-directed-loop α Y)
        ( inv-htpy (triangle-comparison-free-directed-loop α Y))
        ( is-equiv-map-equiv
          ( compute-free-dependent-directed-loop-constant-type-family α Y))
        ( I (λ _ → Y))
```

### The induction principle of the directed circle implies the universal property of the directed circle

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-directed-loop X)
  where

  abstract
    universal-property-induction-principle-directed-circle :
      induction-principle-directed-circle α →
      universal-property-directed-circle α
    universal-property-induction-principle-directed-circle X =
      universal-property-dependent-universal-property-directed-circle α
        ( dependent-universal-property-induction-principle-directed-circle α X)
```
