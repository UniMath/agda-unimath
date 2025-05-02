# Lipschitz functions between metric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.lipschitz-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sequences
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces
```

</details>

## Idea

A positive rational `α : ℚ⁺` is a
{{#concept "Lipschitz constant" Disambiguation="of a function between metric spaces" Agda=lipschitz-constant-function-Metric-Space}}
of a [function](metric-spaces.functions-metric-spaces.md) `f : A → B` between
[metric spaces](metric-spaces.metric-spaces.md) if for any `x y : A`, if `d` is
an upper bound of the distance between `x` and `y` in `A`, `α * d` is an upper
bound on the distance between `f x` and `f y` in `B`. A function which admits a
Lipschitz constant is called a
{{#concept "Lipschitz function" Disambiguation="between metric spaces" WD="Lipschitz function" WDID=Q652707 Agda=is-lipschitz-function-metric-Space}}.

## Definitions

### The property of being a Lipschitz constant of a map between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : map-type-Metric-Space A B)
  where

  is-lipschitz-constant-prop-function-Metric-Space :
    ℚ⁺ → Prop (l1 ⊔ l2 ⊔ l2')
  is-lipschitz-constant-prop-function-Metric-Space α =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        Π-Prop
          ( type-Metric-Space A)
          ( λ x →
            Π-Prop
            ( type-Metric-Space A)
            ( λ y →
              hom-Prop
                ( structure-Metric-Space A d x y)
                ( structure-Metric-Space B (α *ℚ⁺ d) (f x) (f y)))))

  is-lipschitz-constant-function-Metric-Space : ℚ⁺ → UU (l1 ⊔ l2 ⊔ l2')
  is-lipschitz-constant-function-Metric-Space α =
    type-Prop (is-lipschitz-constant-prop-function-Metric-Space α)

  is-prop-is-lipschitz-constant-function-Metric-Space :
    (α : ℚ⁺) →
    is-prop (is-lipschitz-constant-function-Metric-Space α)
  is-prop-is-lipschitz-constant-function-Metric-Space α =
    is-prop-type-Prop (is-lipschitz-constant-prop-function-Metric-Space α)

  lipschitz-constant-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l2')
  lipschitz-constant-function-Metric-Space =
    type-subtype is-lipschitz-constant-prop-function-Metric-Space
```

### The property of being a Lipschitz function

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  is-lipschitz-prop-function-Metric-Space :
    map-type-Metric-Space A B → Prop (l1 ⊔ l2 ⊔ l2')
  is-lipschitz-prop-function-Metric-Space f =
    is-inhabited-subtype-Prop
      (is-lipschitz-constant-prop-function-Metric-Space A B f)

  is-lipschitz-function-Metric-Space :
    map-type-Metric-Space A B → UU (l1 ⊔ l2 ⊔ l2')
  is-lipschitz-function-Metric-Space f =
    type-Prop (is-lipschitz-prop-function-Metric-Space f)

  is-prop-is-lipschitz-function-Metric-Space :
    (f : map-type-Metric-Space A B) →
    is-prop (is-lipschitz-function-Metric-Space f)
  is-prop-is-lipschitz-function-Metric-Space f =
    is-prop-type-Prop (is-lipschitz-prop-function-Metric-Space f)
```

## Properties

### Short functions are Lipschitz functions with Lipschitz constant equal to 1

TODO

### Lipschitz functions are uniformly continuous

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : map-type-Metric-Space A B)
  where

  modulus-of-uniform-continuity-lipschitz-constant-function-Metric-Space :
    lipschitz-constant-function-Metric-Space A B f →
    modulus-of-uniform-continuity-function-Metric-Space A B f
  modulus-of-uniform-continuity-lipschitz-constant-function-Metric-Space
    (α , L) =
    ( mul-ℚ⁺ (inv-ℚ⁺ α)) ,
    ( λ x d y H →
      tr
        ( is-upper-bound-dist-Metric-Space B (f x) (f y))
        ( ( inv (associative-mul-ℚ⁺ α (inv-ℚ⁺ α) d)) ∙
          ( ap (λ y → y *ℚ⁺ d) (right-inverse-law-mul-ℚ⁺ α)) ∙
          ( left-unit-law-mul-ℚ⁺ d))
        ( L (inv-ℚ⁺ α *ℚ⁺ d) x y H))

  is-uniformly-continuous-is-lipschitz-function-Metric-Space :
    is-lipschitz-function-Metric-Space A B f →
    is-uniformly-continuous-map-Metric-Space A B f
  is-uniformly-continuous-is-lipschitz-function-Metric-Space =
    map-is-inhabited
      modulus-of-uniform-continuity-lipschitz-constant-function-Metric-Space
```

### The product of Lipschitz constant of maps is a Lipschitz constant of their composition

```agda
module _
  {la la' lb lb' lc lc' : Level}
  (A : Metric-Space la la')
  (B : Metric-Space lb lb')
  (C : Metric-Space lc lc')
  (g : map-type-Metric-Space B C)
  (f : map-type-Metric-Space A B)
  where

  mul-comp-lipschitz-constant-function-Metric-Space :
    (α β : ℚ⁺) →
    is-lipschitz-constant-function-Metric-Space B C g α →
    is-lipschitz-constant-function-Metric-Space A B f β →
    is-lipschitz-constant-function-Metric-Space A C (g ∘ f) (α *ℚ⁺ β)
  mul-comp-lipschitz-constant-function-Metric-Space α β Hg Hf d x y Nxy =
    inv-tr
      ( λ ε → neighborhood-Metric-Space C ε (g (f x)) (g (f y)))
      ( associative-mul-ℚ⁺ α β d)
      ( Hg (β *ℚ⁺ d) (f x) (f y) (Hf d x y Nxy))
```

### The composition of Lipschitz maps is Lipschitz

```agda
module _
  {la la' lb lb' lc lc' : Level}
  (A : Metric-Space la la')
  (B : Metric-Space lb lb')
  (C : Metric-Space lc lc')
  where

  comp-is-lipschitz-function-Metric-Space :
    (g : map-type-Metric-Space B C) →
    (f : map-type-Metric-Space A B) →
    is-lipschitz-function-Metric-Space B C g →
    is-lipschitz-function-Metric-Space A B f →
    is-lipschitz-function-Metric-Space A C (g ∘ f)
  comp-is-lipschitz-function-Metric-Space g f Hg Hf =
    rec-trunc-Prop
      ( is-lipschitz-prop-function-Metric-Space A C (g ∘ f))
      ( λ (α , Lg) →
        rec-trunc-Prop
          ( is-lipschitz-prop-function-Metric-Space A C (g ∘ f))
          ( λ (β , Lf) →
            unit-trunc-Prop
              ( ( α *ℚ⁺ β) ,
                ( mul-comp-lipschitz-constant-function-Metric-Space
                  ( A)
                  ( B)
                  ( C)
                  ( g)
                  ( f)
                  ( α)
                  ( β)
                  ( Lg)
                  ( Lf))))
          ( Hf))
      ( Hg)
```

## External links

- [Lipschitz maps](https://en.wikipedia.org/wiki/Lipschitz_continuity) at
  Wikipedia
