# Accumulation points of subsets of located metric spaces

```agda
module metric-spaces.accumulation-points-subsets-located-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.intersections-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import lists.sequences

open import logic.functoriality-existential-quantification

open import metric-spaces.action-on-cauchy-approximations-short-maps-metric-spaces
open import metric-spaces.apartness-located-metric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.closed-subsets-located-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-modulated-cauchy-sequences-metric-spaces
open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.located-metric-spaces
open import metric-spaces.modulated-cauchy-sequences-metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

An
{{#concept "accumulation point" WDID=Q858223 WD="limit point" Disambiguation="of a subset of a located metric space" Agda=accumulation-point-subset-Located-Metric-Space}}
of a subset `S` of a
[located metric space](metric-spaces.located-metric-spaces.md) `X` is a point
`x : X` such that there exists a
[Cauchy approximation](metric-spaces.cauchy-approximations-metric-spaces.md) `a`
with [limit](metric-spaces.limits-of-cauchy-approximations-metric-spaces.md) `x`
such that for every `ε : ℚ⁺`, `a ε` is in `S` and is
[apart](metric-spaces.apartness-located-metric-spaces.md) from `x`. In
particular, this implies an accumulation point is not isolated.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (X : Located-Metric-Space l1 l2)
  (S : subset-Located-Metric-Space l3 X)
  where

  is-accumulation-to-point-prop-subset-Located-Metric-Space :
    type-Located-Metric-Space X →
    subtype
      ( l2)
      ( cauchy-approximation-Metric-Space (subspace-Located-Metric-Space X S))
  is-accumulation-to-point-prop-subset-Located-Metric-Space x a =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        apart-prop-Located-Metric-Space X
          ( pr1
            ( map-cauchy-approximation-Metric-Space
              ( subspace-Located-Metric-Space X S)
              ( a)
              ( ε)))
          ( x)) ∧
    is-limit-cauchy-approximation-prop-Metric-Space
      ( metric-space-Located-Metric-Space X)
      ( map-cauchy-approximation-short-map-Metric-Space
        ( subspace-Located-Metric-Space X S)
        ( metric-space-Located-Metric-Space X)
        ( short-inclusion-subspace-Metric-Space
          ( metric-space-Located-Metric-Space X)
          ( S))
        ( a))
      ( x)

  is-accumulation-to-point-subset-Located-Metric-Space :
    type-Located-Metric-Space X →
    cauchy-approximation-Metric-Space (subspace-Located-Metric-Space X S) →
    UU l2
  is-accumulation-to-point-subset-Located-Metric-Space x a =
    type-Prop (is-accumulation-to-point-prop-subset-Located-Metric-Space x a)

  is-accumulation-point-prop-subset-Located-Metric-Space :
    subset-Metric-Space (l1 ⊔ l2 ⊔ l3) (metric-space-Located-Metric-Space X)
  is-accumulation-point-prop-subset-Located-Metric-Space x =
    ∃ ( cauchy-approximation-Metric-Space (subspace-Located-Metric-Space X S))
      ( is-accumulation-to-point-prop-subset-Located-Metric-Space x)

  is-accumulation-point-subset-Located-Metric-Space :
    type-Located-Metric-Space X → UU (l1 ⊔ l2 ⊔ l3)
  is-accumulation-point-subset-Located-Metric-Space x =
    type-Prop (is-accumulation-point-prop-subset-Located-Metric-Space x)

  accumulation-point-subset-Located-Metric-Space : UU (l1 ⊔ l2 ⊔ l3)
  accumulation-point-subset-Located-Metric-Space =
    type-subtype is-accumulation-point-prop-subset-Located-Metric-Space
```

## Properties

### A closed subset of a metric space contains all its accumulation points

```agda
module _
  {l1 l2 l3 : Level}
  (X : Located-Metric-Space l1 l2)
  (S : closed-subset-Located-Metric-Space l3 X)
  where

  is-in-closed-subset-is-accumulation-point-Located-Metric-Space :
    (x : type-Located-Metric-Space X) →
    is-accumulation-point-subset-Located-Metric-Space
      ( X)
      ( subset-closed-subset-Located-Metric-Space X S)
      ( x) →
    is-in-closed-subset-Located-Metric-Space X S x
  is-in-closed-subset-is-accumulation-point-Located-Metric-Space x is-acc-x =
    is-closed-subset-closed-subset-Located-Metric-Space
      ( X)
      ( S)
      ( x)
      ( λ ε →
        let
          open
            do-syntax-trunc-Prop
              ( ∃
                ( type-Located-Metric-Space X)
                ( λ y →
                  neighborhood-prop-Located-Metric-Space X ε x y ∧
                  subset-closed-subset-Located-Metric-Space X S y))
        in do
          (approx@(a , _) , a#x , lim-a=x) ← is-acc-x
          let (y , y∈S) = a ε
          intro-exists
            ( y)
            ( symmetric-neighborhood-Located-Metric-Space X
              ( ε)
              ( y)
              ( x)
              ( saturated-is-limit-cauchy-approximation-Metric-Space
                ( metric-space-Located-Metric-Space X)
                ( map-cauchy-approximation-short-map-Metric-Space
                  ( subspace-Located-Metric-Space
                    ( X)
                    ( subset-closed-subset-Located-Metric-Space X S))
                  ( metric-space-Located-Metric-Space X)
                  ( short-inclusion-subspace-Metric-Space
                    ( metric-space-Located-Metric-Space X)
                    ( subset-closed-subset-Located-Metric-Space X S))
                  ( approx))
                ( x)
                ( lim-a=x)
                ( ε)) ,
              y∈S))
```

### The property of being a sequential accumulation point

```agda
module _
  {l1 l2 l3 : Level}
  (X : Located-Metric-Space l1 l2)
  (S : subset-Located-Metric-Space l3 X)
  (x : type-Located-Metric-Space X)
  where

  is-sequence-accumulating-to-point-prop-subset-Located-Metric-Space :
    subtype l2 (sequence (type-subtype S))
  is-sequence-accumulating-to-point-prop-subset-Located-Metric-Space a =
    Π-Prop ℕ (λ n → apart-prop-Located-Metric-Space X (pr1 (a n)) x) ∧
    is-limit-prop-sequence-Metric-Space
      ( metric-space-Located-Metric-Space X)
      ( pr1 ∘ a)
      ( x)

  is-sequence-accumulating-to-point-subset-Located-Metric-Space :
    sequence (type-subtype S) → UU l2
  is-sequence-accumulating-to-point-subset-Located-Metric-Space =
    is-in-subtype
      ( is-sequence-accumulating-to-point-prop-subset-Located-Metric-Space)

  is-sequential-accumulation-point-prop-subset-Located-Metric-Space :
    Prop (l1 ⊔ l2 ⊔ l3)
  is-sequential-accumulation-point-prop-subset-Located-Metric-Space =
    ∃ ( sequence (type-subtype S))
      ( is-sequence-accumulating-to-point-prop-subset-Located-Metric-Space)

  is-sequential-accumulation-point-subset-Located-Metric-Space :
    UU (l1 ⊔ l2 ⊔ l3)
  is-sequential-accumulation-point-subset-Located-Metric-Space =
    type-Prop is-sequential-accumulation-point-prop-subset-Located-Metric-Space
```

### If `x` is an accumulation point of `S`, it is a sequential accumulation point of `S`

```agda
module _
  {l1 l2 l3 : Level}
  (X : Located-Metric-Space l1 l2)
  (S : subset-Located-Metric-Space l3 X)
  (x : type-Located-Metric-Space X)
  where

  abstract
    is-sequential-accumulation-point-is-accumulation-point-subset-Located-Metric-Space :
      is-accumulation-point-subset-Located-Metric-Space X S x →
      is-sequential-accumulation-point-subset-Located-Metric-Space X S x
    is-sequential-accumulation-point-is-accumulation-point-subset-Located-Metric-Space =
      map-exists
        ( _)
        ( seq-modulated-cauchy-sequence-cauchy-approximation-Metric-Space
          ( subspace-Located-Metric-Space X S))
        ( λ a (a#x , lim-a=x) →
          ( ( λ n → a#x _) ,
            is-limit-modulated-cauchy-sequence-cauchy-approximation-Metric-Space
              ( metric-space-Located-Metric-Space X)
              ( map-cauchy-approximation-short-map-Metric-Space
                ( subspace-Located-Metric-Space X S)
                ( metric-space-Located-Metric-Space X)
                ( short-inclusion-subspace-Metric-Space
                  ( metric-space-Located-Metric-Space X)
                  ( S))
                ( a))
              ( x)
              ( lim-a=x)))
```

### If `x` is a sequential accumulation point of `S`, it is an accumulation point of `S`

```agda
module _
  {l1 l2 l3 : Level}
  (X : Located-Metric-Space l1 l2)
  (S : subset-Located-Metric-Space l3 X)
  (x : type-Located-Metric-Space X)
  where

  abstract
    is-accumulation-point-is-sequential-accumulation-point-subset-Located-Metric-Space :
      is-sequential-accumulation-point-subset-Located-Metric-Space X S x →
      is-accumulation-point-subset-Located-Metric-Space X S x
    is-accumulation-point-is-sequential-accumulation-point-subset-Located-Metric-Space
      is-seq-acc-x =
      let
        open
          do-syntax-trunc-Prop
            ( is-accumulation-point-prop-subset-Located-Metric-Space X S x)
      in do
        (σ , σ#x , lim-σ=x) ← is-seq-acc-x
        μ@(mod-μ , is-mod-μ) ← lim-σ=x
        intro-exists
          ( cauchy-approximation-modulated-cauchy-sequence-Metric-Space
            ( subspace-Located-Metric-Space X S)
            ( σ ,
              cauchy-modulus-limit-modulus-sequence-Metric-Space
                ( metric-space-Located-Metric-Space X)
                ( pr1 ∘ σ)
                ( x)
                ( μ)))
          ( ( λ ε → σ#x _) ,
            ( λ ε δ →
              let ε' = modulus-le-double-le-ℚ⁺ ε
              in
                monotonic-neighborhood-Located-Metric-Space
                  ( X)
                  ( pr1 (σ (mod-μ ε')))
                  ( x)
                  ( ε')
                  ( ε +ℚ⁺ δ)
                  ( transitive-le-ℚ _ _ _
                    ( le-left-add-ℚ⁺ ε δ)
                    ( le-modulus-le-double-le-ℚ⁺ ε))
                  ( is-mod-μ ε' (mod-μ ε') (refl-leq-ℕ (mod-μ ε')))))
```

### Being an accumulation point is equivalent to being a sequential accumulation point

```agda
module _
  {l1 l2 l3 : Level}
  (X : Located-Metric-Space l1 l2)
  (S : subset-Located-Metric-Space l3 X)
  (x : type-Located-Metric-Space X)
  where

  is-accumulation-point-iff-is-sequential-accumulation-point-subset-Located-Metric-Space :
    is-accumulation-point-subset-Located-Metric-Space X S x ↔
    is-sequential-accumulation-point-subset-Located-Metric-Space X S x
  is-accumulation-point-iff-is-sequential-accumulation-point-subset-Located-Metric-Space =
    ( is-sequential-accumulation-point-is-accumulation-point-subset-Located-Metric-Space
        ( X)
        ( S)
        ( x) ,
      is-accumulation-point-is-sequential-accumulation-point-subset-Located-Metric-Space
        ( X)
        ( S)
        ( x))
```

## External links

- [Accumulation point](https://en.wikipedia.org/wiki/Accumulation_point) on
  Wikipedia
