# Cauchy sequences in metric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.cauchy-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.modulated-cauchy-sequences-metric-spaces
open import metric-spaces.modulated-uniformly-continuous-maps-metric-spaces
open import metric-spaces.sequences-metric-spaces
open import metric-spaces.short-maps-metric-spaces
```

</details>

## Idea

A
{{#concept "Cauchy sequence" Disambiguation="in a metric space" WD="cauchy sequence" WDID=Q217847 Agda=cauchy-sequence-Metric-Space}}
`x` in a [metric space](metric-spaces.metric-spaces.md) `X` is a
[sequence](metric-spaces.sequences-metric-spaces.md) of elements of `X` such
that there [exists](foundation.propositional-truncations.md) a
[modulus](metric-spaces.modulated-cauchy-sequences-metric-spaces.md) making it a
modulated Cauchy sequence.

## Definition

### Cauchy sequences

```agda
module _
  {l1 l2 : Level}
  (X : Metric-Space l1 l2)
  (x : sequence-type-Metric-Space X)
  where

  is-cauchy-sequence-prop-Metric-Space : Prop l2
  is-cauchy-sequence-prop-Metric-Space =
    trunc-Prop (cauchy-modulus-sequence-Metric-Space X x)

  is-cauchy-sequence-Metric-Space : UU l2
  is-cauchy-sequence-Metric-Space =
    type-Prop is-cauchy-sequence-prop-Metric-Space

cauchy-sequence-Metric-Space :
  {l1 l2 : Level} → Metric-Space l1 l2 → UU (l1 ⊔ l2)
cauchy-sequence-Metric-Space X =
  type-subtype (is-cauchy-sequence-prop-Metric-Space X)

cauchy-sequence-modulated-cauchy-sequence-Metric-Space :
  {l1 l2 : Level} (M : Metric-Space l1 l2) →
  modulated-cauchy-sequence-Metric-Space M →
  cauchy-sequence-Metric-Space M
cauchy-sequence-modulated-cauchy-sequence-Metric-Space
  M (x , μx) = (x , unit-trunc-Prop μx)

module _
  {l1 l2 : Level}
  (X : Metric-Space l1 l2)
  (x : cauchy-sequence-Metric-Space X)
  where

  seq-cauchy-sequence-Metric-Space : sequence-type-Metric-Space X
  seq-cauchy-sequence-Metric-Space = pr1 x

  is-cauchy-sequence-seq-cauchy-sequence-Metric-Space :
    is-cauchy-sequence-Metric-Space X seq-cauchy-sequence-Metric-Space
  is-cauchy-sequence-seq-cauchy-sequence-Metric-Space = pr2 x
```

## Properties

### A sequence with a limit is Cauchy

```agda
module _
  {l1 l2 : Level}
  (X : Metric-Space l1 l2)
  {x : sequence-type-Metric-Space X}
  where

  abstract
    is-cauchy-has-limit-sequence-Metric-Space :
      has-limit-sequence-Metric-Space X x → is-cauchy-sequence-Metric-Space X x
    is-cauchy-has-limit-sequence-Metric-Space (lim , is-lim-x) =
      map-trunc-Prop
        ( has-cauchy-modulus-has-limit-modulus-sequence-Metric-Space X x lim)
        ( is-lim-x)
```

### If the Cauchy sequence associated with a Cauchy approximation has a limit modulus at `l`, its associated approximation converges to `l`

```agda
module _
  { l1 l2 : Level} (M : Metric-Space l1 l2)
  ( x : cauchy-approximation-Metric-Space M)
  ( lim : type-Metric-Space M)
  ( H :
    limit-modulus-sequence-Metric-Space
      ( M)
      ( map-cauchy-sequence-Metric-Space
        ( M)
        ( cauchy-sequence-cauchy-approximation-Metric-Space M x))
      ( lim))
  where

  abstract
    is-limit-cauchy-approximation-limit-modulus-cauchy-sequence-cauchy-approximation-Metric-Space :
      is-limit-cauchy-approximation-Metric-Space M x lim

    is-limit-cauchy-approximation-limit-modulus-cauchy-sequence-cauchy-approximation-Metric-Space
      ε⁺@(ε , _) δ⁺@(δ , _) =
      let
        (δ'⁺@(δ' , _) , 2δ'<δ) = bound-double-le-ℚ⁺ δ⁺
        (n₁' , 1/n₁'<δ') = smaller-reciprocal-ℚ⁺ δ'⁺
        1/n₁' = positive-reciprocal-rational-ℕ⁺ n₁'
        n₁ = pred-ℕ⁺ n₁'
        n₂ = modulus-limit-modulus-sequence-Metric-Space
          ( M)
          ( map-cauchy-sequence-Metric-Space
            ( M)
            ( cauchy-sequence-cauchy-approximation-Metric-Space M x))
          ( lim)
          ( H)
          ( δ'⁺)
        n = max-ℕ n₁ n₂
        n' = succ-nonzero-ℕ' n
        1/n' = positive-reciprocal-rational-ℕ⁺ n'
        xε = map-cauchy-approximation-Metric-Space M x ε⁺
        x1/n' = map-cauchy-approximation-Metric-Space M x 1/n'
        x1/n'-l-neighborhood :
          neighborhood-Metric-Space M δ'⁺ x1/n' lim
        x1/n'-l-neighborhood =
          is-modulus-limit-modulus-sequence-Metric-Space
            ( M)
            ( map-cauchy-sequence-Metric-Space
              ( M)
              ( cauchy-sequence-cauchy-approximation-Metric-Space M x))
            ( lim)
            ( H)
            ( δ'⁺)
            ( n)
            ( right-leq-max-ℕ n₁ n₂)
      in
        monotonic-neighborhood-Metric-Space
          ( M)
          ( xε)
          ( lim)
          ( (ε⁺ +ℚ⁺ δ'⁺) +ℚ⁺ δ'⁺)
          ( ε⁺ +ℚ⁺ δ⁺)
          ( inv-tr
            ( λ y → le-ℚ⁺ y (ε⁺ +ℚ⁺ δ⁺))
            ( associative-add-ℚ⁺ ε⁺ δ'⁺ δ'⁺)
            ( preserves-le-right-add-ℚ ε (δ' +ℚ δ') δ 2δ'<δ))
          ( triangular-neighborhood-Metric-Space
            ( M)
            ( xε)
            ( x1/n')
            ( lim)
            ( ε⁺ +ℚ⁺ δ'⁺)
            ( δ'⁺)
            ( x1/n'-l-neighborhood)
            ( monotonic-neighborhood-Metric-Space
              ( M)
              ( xε)
              ( x1/n')
              ( ε⁺ +ℚ⁺ 1/n')
              ( ε⁺ +ℚ⁺ δ'⁺)
              ( preserves-le-right-add-ℚ
                ( ε)
                ( rational-ℚ⁺ 1/n')
                ( δ')
                ( concatenate-leq-le-ℚ
                  ( rational-ℚ⁺ 1/n')
                  ( rational-ℚ⁺ 1/n₁')
                  ( δ')
                  ( leq-reciprocal-rational-ℕ⁺
                    ( n₁')
                    ( n')
                    ( reflects-leq-pred-nonzero-ℕ
                      ( n₁')
                      ( n')
                      ( inv-tr
                        ( leq-ℕ n₁)
                        ( is-section-pred-nonzero-ℕ n)
                        ( left-leq-max-ℕ n₁ n₂))))
                  ( 1/n₁'<δ')))
              ( is-cauchy-approximation-map-cauchy-approximation-Metric-Space
                ( M)
                ( x)
                ( ε⁺)
                ( 1/n'))))
```

### If the Cauchy sequence associated with a Cauchy approximation has a limit, the approximation has the same limit

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x : cauchy-approximation-Metric-Space M)
  (lim : type-Metric-Space M)
  where

  abstract
    is-limit-cauchy-approximation-limit-cauchy-sequence-cauchy-approximation-Metric-Space :
      is-limit-cauchy-sequence-Metric-Space
        ( M)
        ( cauchy-sequence-cauchy-approximation-Metric-Space M x)
        ( lim) →
      is-limit-cauchy-approximation-Metric-Space M x lim
    is-limit-cauchy-approximation-limit-cauchy-sequence-cauchy-approximation-Metric-Space
      =
        rec-trunc-Prop
          ( is-limit-cauchy-approximation-prop-Metric-Space M x lim)
          ( is-limit-cauchy-approximation-limit-modulus-cauchy-sequence-cauchy-approximation-Metric-Space
            ( M)
            ( x)
            ( lim))
```

### Modulated uniformly continuous maps between metric spaces preserve Cauchy sequences

```agda
module _
  {l1 l2 l1' l2' : Level} (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : modulated-ucont-map-Metric-Space A B)
  (u : cauchy-sequence-Metric-Space A)
  where

  seq-modulated-ucont-map-cauchy-sequence-Metric-Space :
    sequence-type-Metric-Space B
  seq-modulated-ucont-map-cauchy-sequence-Metric-Space =
    map-sequence
      ( map-modulated-ucont-map-Metric-Space A B f)
      ( map-cauchy-sequence-Metric-Space A u)

  abstract
    is-cauchy-seq-modulated-ucont-map-cauchy-sequence-Metric-Space :
      is-cauchy-sequence-Metric-Space B
        ( seq-modulated-ucont-map-cauchy-sequence-Metric-Space)
    is-cauchy-seq-modulated-ucont-map-cauchy-sequence-Metric-Space ε =
      ( modulus-of-convergence-cauchy-sequence-Metric-Space A u
          (modulus-modulated-ucont-map-Metric-Space A B f ε) ,
        λ m n M≤m M≤n →
          is-modulus-of-uniform-continuity-map-modulus-modulated-ucont-map-Metric-Space
            ( A)
            ( B)
            ( f)
            ( map-cauchy-sequence-Metric-Space A u m)
            ( ε)
            ( map-cauchy-sequence-Metric-Space A u n)
            ( neighborhood-modulus-of-convergence-cauchy-sequence-Metric-Space
              ( A)
              ( u)
              ( modulus-modulated-ucont-map-Metric-Space A B f ε)
              ( m)
              ( n)
              ( M≤m)
              ( M≤n)))

  map-modulated-ucont-map-cauchy-sequence-Metric-Space :
    cauchy-sequence-Metric-Space B
  map-modulated-ucont-map-cauchy-sequence-Metric-Space =
    ( seq-modulated-ucont-map-cauchy-sequence-Metric-Space ,
      is-cauchy-seq-modulated-ucont-map-cauchy-sequence-Metric-Space)
```

### Short maps between metric spaces preserve Cauchy sequences

```agda
module _
  {l1 l2 l1' l2' : Level} (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : short-map-Metric-Space A B)
  (u : cauchy-sequence-Metric-Space A)
  where

  map-short-map-cauchy-sequence-Metric-Space : cauchy-sequence-Metric-Space B
  map-short-map-cauchy-sequence-Metric-Space =
    map-modulated-ucont-map-cauchy-sequence-Metric-Space A B
      ( modulated-ucont-map-short-map-Metric-Space A B f)
      ( u)
```

### Pairing of Cauchy sequences

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  (u : cauchy-sequence-Metric-Space A)
  (v : cauchy-sequence-Metric-Space B)
  where

  seq-pair-cauchy-sequence-Metric-Space :
    sequence-type-Metric-Space (product-Metric-Space A B)
  seq-pair-cauchy-sequence-Metric-Space =
    pair-sequence
      ( seq-cauchy-sequence-Metric-Space A u)
      ( seq-cauchy-sequence-Metric-Space B v)

  abstract
    is-cauchy-seq-pair-cauchy-sequence-Metric-Space :
      is-cauchy-sequence-Metric-Space
        ( product-Metric-Space A B)
        ( seq-pair-cauchy-sequence-Metric-Space)
    is-cauchy-seq-pair-cauchy-sequence-Metric-Space =
      let
        open
          do-syntax-trunc-Prop
            ( is-cauchy-sequence-prop-Metric-Space
              ( product-Metric-Space A B)
              ( seq-pair-cauchy-sequence-Metric-Space))
      in do
        μ-u ← is-cauchy-sequence-seq-cauchy-sequence-Metric-Space A u
        μ-v ← is-cauchy-sequence-seq-cauchy-sequence-Metric-Space B v
        unit-trunc-Prop
          ( is-cauchy-seq-pair-modulated-cauchy-sequence-Metric-Space
            ( A)
            ( B)
            ( seq-cauchy-sequence-Metric-Space A u , μ-u)
            ( seq-cauchy-sequence-Metric-Space B v , μ-v))

  pair-cauchy-sequence-Metric-Space :
    cauchy-sequence-Metric-Space (product-Metric-Space A B)
  pair-cauchy-sequence-Metric-Space =
    ( seq-pair-cauchy-sequence-Metric-Space ,
      is-cauchy-seq-pair-cauchy-sequence-Metric-Space)
```

### To show a sequence `a` is Cauchy, it suffices to have a modulus function `μ` such that for any `ε`, `a (μ ε)` and `a (μ ε + k)` are in an `ε`-neighborhood

```agda
module
  _
  {l1 l2 : Level}
  (X : Metric-Space l1 l2)
  (a : sequence-type-Metric-Space X)
  (μ : ℚ⁺ → ℕ)
  where

  abstract
    is-cauchy-sequence-modulus-neighborhood-add-sequence-Metric-Space :
      ( (ε : ℚ⁺) (k : ℕ) →
        neighborhood-Metric-Space X ε (a (μ ε)) (a (μ ε +ℕ k))) →
      is-cauchy-sequence-Metric-Space X a
    is-cauchy-sequence-modulus-neighborhood-add-sequence-Metric-Space H =
      unit-trunc-Prop
        ( cauchy-modulus-neighborhood-add-sequence-Metric-Space X a μ H)
```

## See also

- [Cauchy sequences in complete metric spaces](metric-spaces.cauchy-sequences-complete-metric-spaces.md)

## External links

- [Cauchy sequences](https://en.wikipedia.org/wiki/Cauchy_sequence) at Wikipedia
