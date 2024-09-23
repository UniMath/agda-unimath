# Cospans of synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.cospans-synthetic-categories where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.globular-types

open import synthetic-category-theory.synthetic-categories
```

</details>

## Idea

A cospan is a pair of functors f, g with a common codomain:

```text
C --f--> E <--g-- D
```

## Definition

```agda
module _
  {l : Level}
  where

  cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (C E D : category-Synthetic-Category-Theory κ) → UU l
  cospan-Synthetic-Category-Theory κ C E D =
    Σ ( functor-Synthetic-Category-Theory κ C E)
      λ f → functor-Synthetic-Category-Theory κ D E
```

### The components of a cospan

```agda
  left-source-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C E D : category-Synthetic-Category-Theory κ} →
    cospan-Synthetic-Category-Theory κ C E D →
      category-Synthetic-Category-Theory κ
  left-source-cospan-Synthetic-Category-Theory κ {C = C} S = C

  right-source-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C E D : category-Synthetic-Category-Theory κ} →
    cospan-Synthetic-Category-Theory κ C E D →
      category-Synthetic-Category-Theory κ
  right-source-cospan-Synthetic-Category-Theory κ {D = D} S = D

  target-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C E D : category-Synthetic-Category-Theory κ} →
    cospan-Synthetic-Category-Theory κ C E D →
    category-Synthetic-Category-Theory κ
  target-cospan-Synthetic-Category-Theory κ {E = E} S = E

  left-map-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C E D : category-Synthetic-Category-Theory κ}
    (S : cospan-Synthetic-Category-Theory κ C E D) →
    functor-Synthetic-Category-Theory κ
      ( left-source-cospan-Synthetic-Category-Theory κ S)
      ( target-cospan-Synthetic-Category-Theory κ S)
  left-map-cospan-Synthetic-Category-Theory κ = pr1

  right-map-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C E D : category-Synthetic-Category-Theory κ}
    (S : cospan-Synthetic-Category-Theory κ C E D) →
    functor-Synthetic-Category-Theory κ
      ( right-source-cospan-Synthetic-Category-Theory κ S)
      ( target-cospan-Synthetic-Category-Theory κ S)
  right-map-cospan-Synthetic-Category-Theory κ = pr2
```

## Transformations of cone diagrams

A transformation between cospans C --f--> E <--g-- D and C'--f'--> E' <--g'-- D'
is a commutative diagram of the form:

```text
C --f---> E <---g-- D
|         |         |
φ   τ⇙    χ    σ⇙   ψ
|         |         |
v         v         v
C'--f'--> E' <--g'--D'
```

```agda
module _
  {l : Level}
  where

  transformation-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    (S : cospan-Synthetic-Category-Theory κ C E D)
    (S' : cospan-Synthetic-Category-Theory κ C' E' D') → UU l
  transformation-cospan-Synthetic-Category-Theory κ μ S S' =
    Σ ( functor-Synthetic-Category-Theory κ
        ( left-source-cospan-Synthetic-Category-Theory κ S)
        ( left-source-cospan-Synthetic-Category-Theory κ S'))
    λ φ →
      Σ ( functor-Synthetic-Category-Theory κ
          ( target-cospan-Synthetic-Category-Theory κ S)
          ( target-cospan-Synthetic-Category-Theory κ S'))
      λ χ →
        Σ ( functor-Synthetic-Category-Theory κ
            ( right-source-cospan-Synthetic-Category-Theory κ S)
            ( right-source-cospan-Synthetic-Category-Theory κ S'))
        λ ψ →
          Σ ( commuting-square-functors-Synthetic-Category-Theory κ μ
              ( left-map-cospan-Synthetic-Category-Theory κ S)
              ( χ)
              ( φ)
              ( left-map-cospan-Synthetic-Category-Theory κ S'))
            λ τ →
              commuting-square-functors-Synthetic-Category-Theory κ μ
                ( right-map-cospan-Synthetic-Category-Theory κ S)
                ( χ)
                ( ψ)
                ( right-map-cospan-Synthetic-Category-Theory κ S')
```

## The components of a transformation of cospans

```agda
module _
  {l : Level}
  where

  left-map-transformation-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    {S : cospan-Synthetic-Category-Theory κ C E D}
    {S' : cospan-Synthetic-Category-Theory κ C' E' D'} →
    transformation-cospan-Synthetic-Category-Theory κ μ S S' →
      functor-Synthetic-Category-Theory κ
        ( left-source-cospan-Synthetic-Category-Theory κ S)
        ( left-source-cospan-Synthetic-Category-Theory κ S')
  left-map-transformation-cospan-Synthetic-Category-Theory κ μ H = pr1 H

  right-map-transformation-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    {S : cospan-Synthetic-Category-Theory κ C E D}
    {S' : cospan-Synthetic-Category-Theory κ C' E' D'} →
    transformation-cospan-Synthetic-Category-Theory κ μ S S' →
      functor-Synthetic-Category-Theory κ
        ( right-source-cospan-Synthetic-Category-Theory κ S)
        ( right-source-cospan-Synthetic-Category-Theory κ S')
  right-map-transformation-cospan-Synthetic-Category-Theory κ μ H =
    pr1 (pr2 (pr2 H))

  middle-map-transformation-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    {S : cospan-Synthetic-Category-Theory κ C E D}
    {S' : cospan-Synthetic-Category-Theory κ C' E' D'} →
    transformation-cospan-Synthetic-Category-Theory κ μ S S' →
      functor-Synthetic-Category-Theory κ
        ( target-cospan-Synthetic-Category-Theory κ S)
        ( target-cospan-Synthetic-Category-Theory κ S')
  middle-map-transformation-cospan-Synthetic-Category-Theory κ μ H = pr1 (pr2 H)

  left-commuting-square-transformation-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    {S : cospan-Synthetic-Category-Theory κ C E D}
    {S' : cospan-Synthetic-Category-Theory κ C' E' D'}
    (H : transformation-cospan-Synthetic-Category-Theory κ μ S S') →
      commuting-square-functors-Synthetic-Category-Theory κ μ
        ( left-map-cospan-Synthetic-Category-Theory κ S)
        ( middle-map-transformation-cospan-Synthetic-Category-Theory κ μ H)
        ( left-map-transformation-cospan-Synthetic-Category-Theory κ μ H)
        ( left-map-cospan-Synthetic-Category-Theory κ S')
  left-commuting-square-transformation-cospan-Synthetic-Category-Theory κ μ H =
    pr1 (pr2 (pr2 (pr2 H)))

  right-commuting-square-transformation-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    {S : cospan-Synthetic-Category-Theory κ C E D}
    {S' : cospan-Synthetic-Category-Theory κ C' E' D'}
    (H : transformation-cospan-Synthetic-Category-Theory κ μ S S') →
      commuting-square-functors-Synthetic-Category-Theory κ μ
        ( right-map-cospan-Synthetic-Category-Theory κ S)
        ( middle-map-transformation-cospan-Synthetic-Category-Theory κ μ H)
        ( right-map-transformation-cospan-Synthetic-Category-Theory κ μ H)
        ( right-map-cospan-Synthetic-Category-Theory κ S')
  right-commuting-square-transformation-cospan-Synthetic-Category-Theory κ μ H =
    pr2 (pr2 (pr2 (pr2 H)))
```
