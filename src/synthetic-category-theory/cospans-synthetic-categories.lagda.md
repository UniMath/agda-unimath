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

open import synthetic-category-theory.equivalences-synthetic-categories
open import synthetic-category-theory.synthetic-categories
```

</details>

## Idea

A {{#concept "cospan" Disambiguation="Synthetic categories"}} of
[synthetic categories](synthetic-category-theory.synthetic-categories.md) is a
pair of functors f, g of synthetic categories with a common codomain:

```text
C --f--> E <--g-- D.
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
      ( λ f → functor-Synthetic-Category-Theory κ D E)
```

### The components of a cospan of synthetic categories

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

  left-functor-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C E D : category-Synthetic-Category-Theory κ}
    (S : cospan-Synthetic-Category-Theory κ C E D) →
    functor-Synthetic-Category-Theory κ
      ( left-source-cospan-Synthetic-Category-Theory κ S)
      ( target-cospan-Synthetic-Category-Theory κ S)
  left-functor-cospan-Synthetic-Category-Theory κ = pr1

  right-functor-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C E D : category-Synthetic-Category-Theory κ}
    (S : cospan-Synthetic-Category-Theory κ C E D) →
    functor-Synthetic-Category-Theory κ
      ( right-source-cospan-Synthetic-Category-Theory κ S)
      ( target-cospan-Synthetic-Category-Theory κ S)
  right-functor-cospan-Synthetic-Category-Theory κ = pr2
```

## Transformations of cospans of synthetic categories

A transformation between cospans C --f--> E <--g-- D and C'--f'--> E' <--g'-- D'
is commutative diagram of the form:

```text
C --f---> E <---g-- D
|         |         |
φ   τ⇙    χ    σ⇙   ψ
|         |         |
v         v         v
C'--f'--> E' <--g'--D'.
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
      ( λ φ →
        Σ ( functor-Synthetic-Category-Theory κ
            ( target-cospan-Synthetic-Category-Theory κ S)
            ( target-cospan-Synthetic-Category-Theory κ S'))
          ( λ χ →
            Σ ( functor-Synthetic-Category-Theory κ
                ( right-source-cospan-Synthetic-Category-Theory κ S)
                ( right-source-cospan-Synthetic-Category-Theory κ S'))
              ( λ ψ →
                Σ ( commuting-square-functors-Synthetic-Category-Theory κ μ
                    ( left-functor-cospan-Synthetic-Category-Theory κ S)
                    ( χ)
                    ( φ)
                    ( left-functor-cospan-Synthetic-Category-Theory κ S'))
                  ( λ τ →
                    commuting-square-functors-Synthetic-Category-Theory κ μ
                      ( right-functor-cospan-Synthetic-Category-Theory κ S)
                      ( χ)
                      ( ψ)
                      ( right-functor-cospan-Synthetic-Category-Theory κ S')))))
```

### The components of a transformation of cospans of synthetic categories

```agda
module _
  {l : Level}
  where

  left-functor-transformation-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    {S : cospan-Synthetic-Category-Theory κ C E D}
    {S' : cospan-Synthetic-Category-Theory κ C' E' D'} →
    transformation-cospan-Synthetic-Category-Theory κ μ S S' →
    functor-Synthetic-Category-Theory κ
      ( left-source-cospan-Synthetic-Category-Theory κ S)
      ( left-source-cospan-Synthetic-Category-Theory κ S')
  left-functor-transformation-cospan-Synthetic-Category-Theory κ μ H = pr1 H

  right-functor-transformation-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    {S : cospan-Synthetic-Category-Theory κ C E D}
    {S' : cospan-Synthetic-Category-Theory κ C' E' D'} →
    transformation-cospan-Synthetic-Category-Theory κ μ S S' →
    functor-Synthetic-Category-Theory κ
      ( right-source-cospan-Synthetic-Category-Theory κ S)
      ( right-source-cospan-Synthetic-Category-Theory κ S')
  right-functor-transformation-cospan-Synthetic-Category-Theory κ μ H =
    pr1 (pr2 (pr2 H))

  middle-functor-transformation-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    {S : cospan-Synthetic-Category-Theory κ C E D}
    {S' : cospan-Synthetic-Category-Theory κ C' E' D'} →
    transformation-cospan-Synthetic-Category-Theory κ μ S S' →
    functor-Synthetic-Category-Theory κ
      ( target-cospan-Synthetic-Category-Theory κ S)
      ( target-cospan-Synthetic-Category-Theory κ S')
  middle-functor-transformation-cospan-Synthetic-Category-Theory κ μ H =
    pr1 (pr2 H)

  left-commuting-square-transformation-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    {S : cospan-Synthetic-Category-Theory κ C E D}
    {S' : cospan-Synthetic-Category-Theory κ C' E' D'}
    (H : transformation-cospan-Synthetic-Category-Theory κ μ S S') →
    commuting-square-functors-Synthetic-Category-Theory κ μ
      ( left-functor-cospan-Synthetic-Category-Theory κ S)
      ( middle-functor-transformation-cospan-Synthetic-Category-Theory κ μ H)
      ( left-functor-transformation-cospan-Synthetic-Category-Theory κ μ H)
      ( left-functor-cospan-Synthetic-Category-Theory κ S')
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
      ( right-functor-cospan-Synthetic-Category-Theory κ S)
      ( middle-functor-transformation-cospan-Synthetic-Category-Theory κ μ H)
      ( right-functor-transformation-cospan-Synthetic-Category-Theory κ μ H)
      ( right-functor-cospan-Synthetic-Category-Theory κ S')
  right-commuting-square-transformation-cospan-Synthetic-Category-Theory κ μ H =
    pr2 (pr2 (pr2 (pr2 H)))
```

### Equivalences of cospans

An equivalence of cospans S and S' is a transformations between S and S' such
that all three vertical functors are equivalences.

```agda
module _
  {l : Level}
  where

  equiv-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    (S : cospan-Synthetic-Category-Theory κ C E D)
    (S' : cospan-Synthetic-Category-Theory κ C' E' D') → UU l
  equiv-cospan-Synthetic-Category-Theory κ μ ι S S' =
    Σ ( equiv-Synthetic-Category-Theory κ μ ι
        ( left-source-cospan-Synthetic-Category-Theory κ S)
        ( left-source-cospan-Synthetic-Category-Theory κ S'))
      ( λ φ →
        Σ ( equiv-Synthetic-Category-Theory κ μ ι
            ( target-cospan-Synthetic-Category-Theory κ S)
            ( target-cospan-Synthetic-Category-Theory κ S'))
          ( λ χ →
            Σ ( equiv-Synthetic-Category-Theory κ μ ι
                ( right-source-cospan-Synthetic-Category-Theory κ S)
                ( right-source-cospan-Synthetic-Category-Theory κ S'))
              ( λ ψ →
                Σ ( commuting-square-functors-Synthetic-Category-Theory κ μ
                    ( left-functor-cospan-Synthetic-Category-Theory κ S)
                    ( functor-equiv-Synthetic-Category-Theory κ μ ι χ)
                    ( functor-equiv-Synthetic-Category-Theory κ μ ι φ)
                    ( left-functor-cospan-Synthetic-Category-Theory κ S'))
                  ( λ τ →
                    commuting-square-functors-Synthetic-Category-Theory κ μ
                      ( right-functor-cospan-Synthetic-Category-Theory κ S)
                      ( functor-equiv-Synthetic-Category-Theory κ μ ι χ)
                      ( functor-equiv-Synthetic-Category-Theory κ μ ι ψ)
                      ( right-functor-cospan-Synthetic-Category-Theory κ S')))))
```

### The components of an equivalence of cospans of synthetic categories

```agda
module _
  {l : Level}
  where

  left-equiv-equiv-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    {S : cospan-Synthetic-Category-Theory κ C E D}
    {S' : cospan-Synthetic-Category-Theory κ C' E' D'} →
    equiv-cospan-Synthetic-Category-Theory κ μ ι S S' →
    equiv-Synthetic-Category-Theory κ μ ι
      ( left-source-cospan-Synthetic-Category-Theory κ S)
      ( left-source-cospan-Synthetic-Category-Theory κ S')
  left-equiv-equiv-cospan-Synthetic-Category-Theory κ μ ι H = pr1 H

  left-functor-equiv-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    {S : cospan-Synthetic-Category-Theory κ C E D}
    {S' : cospan-Synthetic-Category-Theory κ C' E' D'} →
    equiv-cospan-Synthetic-Category-Theory κ μ ι S S' →
    functor-Synthetic-Category-Theory κ
      ( left-source-cospan-Synthetic-Category-Theory κ S)
      ( left-source-cospan-Synthetic-Category-Theory κ S')
  left-functor-equiv-cospan-Synthetic-Category-Theory κ μ ι H =
    functor-equiv-Synthetic-Category-Theory κ μ ι
      ( left-equiv-equiv-cospan-Synthetic-Category-Theory κ μ ι H)

  middle-equiv-equiv-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    {S : cospan-Synthetic-Category-Theory κ C E D}
    {S' : cospan-Synthetic-Category-Theory κ C' E' D'} →
    equiv-cospan-Synthetic-Category-Theory κ μ ι S S' →
    equiv-Synthetic-Category-Theory κ μ ι
      ( target-cospan-Synthetic-Category-Theory κ S)
      ( target-cospan-Synthetic-Category-Theory κ S')
  middle-equiv-equiv-cospan-Synthetic-Category-Theory κ μ ι H =
    pr1 (pr2 H)

  middle-functor-equiv-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    {S : cospan-Synthetic-Category-Theory κ C E D}
    {S' : cospan-Synthetic-Category-Theory κ C' E' D'} →
    equiv-cospan-Synthetic-Category-Theory κ μ ι S S' →
    functor-Synthetic-Category-Theory κ
      ( target-cospan-Synthetic-Category-Theory κ S)
      ( target-cospan-Synthetic-Category-Theory κ S')
  middle-functor-equiv-cospan-Synthetic-Category-Theory κ μ ι H =
    functor-equiv-Synthetic-Category-Theory κ μ ι
      ( middle-equiv-equiv-cospan-Synthetic-Category-Theory κ μ ι H)

  right-equiv-equiv-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    {S : cospan-Synthetic-Category-Theory κ C E D}
    {S' : cospan-Synthetic-Category-Theory κ C' E' D'} →
    equiv-cospan-Synthetic-Category-Theory κ μ ι S S' →
    equiv-Synthetic-Category-Theory κ μ ι
      ( right-source-cospan-Synthetic-Category-Theory κ S)
      ( right-source-cospan-Synthetic-Category-Theory κ S')
  right-equiv-equiv-cospan-Synthetic-Category-Theory κ μ ι H =
    pr1 (pr2 (pr2 H))

  right-functor-equiv-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    {S : cospan-Synthetic-Category-Theory κ C E D}
    {S' : cospan-Synthetic-Category-Theory κ C' E' D'} →
    equiv-cospan-Synthetic-Category-Theory κ μ ι S S' →
    functor-Synthetic-Category-Theory κ
      ( right-source-cospan-Synthetic-Category-Theory κ S)
      ( right-source-cospan-Synthetic-Category-Theory κ S')
  right-functor-equiv-cospan-Synthetic-Category-Theory κ μ ι H =
    functor-equiv-Synthetic-Category-Theory κ μ ι
      ( right-equiv-equiv-cospan-Synthetic-Category-Theory κ μ ι H)

  left-commuting-square-equiv-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    {S : cospan-Synthetic-Category-Theory κ C E D}
    {S' : cospan-Synthetic-Category-Theory κ C' E' D'}
    (H : equiv-cospan-Synthetic-Category-Theory κ μ ι S S') →
      ( commuting-square-functors-Synthetic-Category-Theory κ μ
        ( left-functor-cospan-Synthetic-Category-Theory κ S)
        ( middle-functor-equiv-cospan-Synthetic-Category-Theory κ μ ι H)
        ( left-functor-equiv-cospan-Synthetic-Category-Theory κ μ ι H)
        ( left-functor-cospan-Synthetic-Category-Theory κ S'))
  left-commuting-square-equiv-cospan-Synthetic-Category-Theory κ μ ι H =
    pr1 (pr2 (pr2 (pr2 H)))

  right-commuting-square-equiv-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    {S : cospan-Synthetic-Category-Theory κ C E D}
    {S' : cospan-Synthetic-Category-Theory κ C' E' D'}
    (H : equiv-cospan-Synthetic-Category-Theory κ μ ι S S') →
      ( commuting-square-functors-Synthetic-Category-Theory κ μ
        ( right-functor-cospan-Synthetic-Category-Theory κ S)
        ( middle-functor-equiv-cospan-Synthetic-Category-Theory κ μ ι H)
        ( right-functor-equiv-cospan-Synthetic-Category-Theory κ μ ι H)
        ( right-functor-cospan-Synthetic-Category-Theory κ S'))
  right-commuting-square-equiv-cospan-Synthetic-Category-Theory κ μ ι H =
    pr2 (pr2 (pr2 (pr2 H)))

  transformation-cospan-equiv-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C C' E E' D D' : category-Synthetic-Category-Theory κ}
    {S : cospan-Synthetic-Category-Theory κ C E D}
    {S' : cospan-Synthetic-Category-Theory κ C' E' D'} →
    equiv-cospan-Synthetic-Category-Theory κ μ ι S S' →
    transformation-cospan-Synthetic-Category-Theory κ μ S S'
  pr1
    ( transformation-cospan-equiv-cospan-Synthetic-Category-Theory κ μ ι H) =
      left-functor-equiv-cospan-Synthetic-Category-Theory κ μ ι H
  pr1 (pr2
    ( transformation-cospan-equiv-cospan-Synthetic-Category-Theory κ μ ι H)) =
      middle-functor-equiv-cospan-Synthetic-Category-Theory κ μ ι H
  pr1 (pr2 (pr2
    (transformation-cospan-equiv-cospan-Synthetic-Category-Theory κ μ ι H))) =
      right-functor-equiv-cospan-Synthetic-Category-Theory κ μ ι H
  pr1 (pr2 (pr2 (pr2
    ( transformation-cospan-equiv-cospan-Synthetic-Category-Theory κ μ ι H)))) =
      left-commuting-square-equiv-cospan-Synthetic-Category-Theory κ μ ι H
  pr2 (pr2 (pr2 (pr2
    ( transformation-cospan-equiv-cospan-Synthetic-Category-Theory κ μ ι H)))) =
      right-commuting-square-equiv-cospan-Synthetic-Category-Theory κ μ ι H
```
