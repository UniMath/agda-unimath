# Modulated Cauchy sequences in metric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.modulated-cauchy-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.modulated-uniformly-continuous-maps-metric-spaces
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

A
{{#concept "modulated Cauchy sequence" Disambiguation="in a metric space" Agda=modulated-cauchy-sequence-Metric-Space}}
`x` in a [metric space](metric-spaces.metric-spaces.md) is a mapping from the
[natural numbers](elementary-number-theory.natural-numbers.md) to the underlying
type of the metric space such that for any
[positive rational](elementary-number-theory.positive-rational-numbers.md) `ε`,
there is a concrete `n : ℕ` such that for any `m, k ≥ n`, `x m` and `x k` are in
an `ε`-neighborhood of each other.

Importantly, this is a structure, not a proposition, allowing us to explicitly
calculate rates of convergence. This follows Section 11.2.2 in {{#cite UF13}}.

In a metric space, every modulated Cauchy sequence has a (non-unique)
corresponding
[Cauchy approximation](metric-spaces.cauchy-approximations-metric-spaces.md),
with the same [limit](metric-spaces.limits-of-sequences-metric-spaces.md) if
either exists, and vice versa.

## Definition

### Modulated Cauchy sequences

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x : sequence-type-Metric-Space M)
  where

  is-cauchy-modulus-sequence-Metric-Space : ℚ⁺ → ℕ → UU l2
  is-cauchy-modulus-sequence-Metric-Space ε N =
    (m k : ℕ) → leq-ℕ N m → leq-ℕ N k →
    neighborhood-Metric-Space M ε (x m) (x k)

  cauchy-modulus-sequence-Metric-Space : UU l2
  cauchy-modulus-sequence-Metric-Space =
    (ε : ℚ⁺) → Σ ℕ (is-cauchy-modulus-sequence-Metric-Space ε)

module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  modulated-cauchy-sequence-Metric-Space : UU (l1 ⊔ l2)
  modulated-cauchy-sequence-Metric-Space =
    Σ ( sequence-type-Metric-Space M)
      ( cauchy-modulus-sequence-Metric-Space M)

  map-modulus-modulated-cauchy-sequence-Metric-Space :
    modulated-cauchy-sequence-Metric-Space → ℚ⁺ → ℕ
  map-modulus-modulated-cauchy-sequence-Metric-Space (x , is-cauchy-x) ε⁺ =
    pr1 (is-cauchy-x ε⁺)

  sequence-modulated-cauchy-sequence-Metric-Space :
    modulated-cauchy-sequence-Metric-Space → sequence-type-Metric-Space M
  sequence-modulated-cauchy-sequence-Metric-Space = pr1

  modulus-modulated-cauchy-sequence-Metric-Space :
    (x : modulated-cauchy-sequence-Metric-Space) →
    cauchy-modulus-sequence-Metric-Space M
      ( sequence-modulated-cauchy-sequence-Metric-Space x)
  modulus-modulated-cauchy-sequence-Metric-Space = pr2

  neighborhood-map-modulus-modulated-cauchy-sequence-Metric-Space :
    (x : modulated-cauchy-sequence-Metric-Space) (ε⁺ : ℚ⁺) (m k : ℕ) →
    leq-ℕ (map-modulus-modulated-cauchy-sequence-Metric-Space x ε⁺) m →
    leq-ℕ (map-modulus-modulated-cauchy-sequence-Metric-Space x ε⁺) k →
    neighborhood-Metric-Space
      ( M)
      ( ε⁺)
      ( sequence-modulated-cauchy-sequence-Metric-Space x m)
      ( sequence-modulated-cauchy-sequence-Metric-Space x k)
  neighborhood-map-modulus-modulated-cauchy-sequence-Metric-Space
    (x , is-cauchy-x) ε⁺ = pr2 (is-cauchy-x ε⁺)

  map-at-map-modulus-modulated-cauchy-sequence-Metric-Space :
    (x : modulated-cauchy-sequence-Metric-Space) (ε⁺ : ℚ⁺) → type-Metric-Space M
  map-at-map-modulus-modulated-cauchy-sequence-Metric-Space x ε⁺ =
    sequence-modulated-cauchy-sequence-Metric-Space
      ( x)
      ( map-modulus-modulated-cauchy-sequence-Metric-Space x ε⁺)

  neighborhood-at-map-modulus-modulated-cauchy-sequence-Metric-Space :
    (x : modulated-cauchy-sequence-Metric-Space) (ε⁺ : ℚ⁺) (m : ℕ) →
    leq-ℕ (map-modulus-modulated-cauchy-sequence-Metric-Space x ε⁺) m →
    neighborhood-Metric-Space
      ( M)
      ( ε⁺)
      ( map-at-map-modulus-modulated-cauchy-sequence-Metric-Space x ε⁺)
      ( sequence-modulated-cauchy-sequence-Metric-Space x m)
  neighborhood-at-map-modulus-modulated-cauchy-sequence-Metric-Space
    x ε⁺ m n≤m =
    let
      n = map-modulus-modulated-cauchy-sequence-Metric-Space x ε⁺
    in
      neighborhood-map-modulus-modulated-cauchy-sequence-Metric-Space
        ( x)
        ( ε⁺)
        ( n)
        ( m)
        ( refl-leq-ℕ n)
        ( n≤m)
```

## Properties

### A sequence with a convergence modulus has a Cauchy modulus

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x : sequence-type-Metric-Space M)
  (lim : type-Metric-Space M)
  (H : limit-modulus-sequence-Metric-Space M x lim)
  where

  cauchy-modulus-limit-modulus-sequence-Metric-Space :
    cauchy-modulus-sequence-Metric-Space M x
  cauchy-modulus-limit-modulus-sequence-Metric-Space ε⁺@(ε , _) =
    let
      (ε'⁺@(ε' , _) , 2ε'<ε) = bound-double-le-ℚ⁺ ε⁺
    in
      ( modulus-limit-modulus-sequence-Metric-Space M x lim H ε'⁺ ,
        λ m k n≤m n≤k →
        monotonic-neighborhood-Metric-Space
          ( M)
          ( x m)
          ( x k)
          ( ε'⁺ +ℚ⁺ ε'⁺)
          ( ε⁺)
          ( 2ε'<ε)
          ( triangular-neighborhood-Metric-Space
            ( M)
            ( x m)
            ( lim)
            ( x k)
            ( ε'⁺)
            ( ε'⁺)
            ( symmetric-neighborhood-Metric-Space
              ( M)
              ( ε'⁺)
              ( x k)
              ( lim)
              ( is-modulus-limit-modulus-sequence-Metric-Space M x
                ( lim)
                ( H)
                ( ε'⁺)
                ( k)
                ( n≤k)))
            ( is-modulus-limit-modulus-sequence-Metric-Space M x
              ( lim)
              ( H)
              ( ε'⁺)
              ( m)
              ( n≤m))))
```

### Correspondence to Cauchy approximations

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x : modulated-cauchy-sequence-Metric-Space M)
  where

  map-cauchy-approximation-modulated-cauchy-sequence-Metric-Space :
    ℚ⁺ → type-Metric-Space M
  map-cauchy-approximation-modulated-cauchy-sequence-Metric-Space ε =
    sequence-modulated-cauchy-sequence-Metric-Space
      ( M)
      ( x)
      ( map-modulus-modulated-cauchy-sequence-Metric-Space M x ε)

  is-cauchy-approximation-map-cauchy-approximation-modulated-cauchy-sequence-Metric-Space :
    is-cauchy-approximation-Metric-Space
      ( M)
      ( map-cauchy-approximation-modulated-cauchy-sequence-Metric-Space)
  is-cauchy-approximation-map-cauchy-approximation-modulated-cauchy-sequence-Metric-Space
    ε⁺@(ε , _) δ⁺@(δ , _) =
    let
      mε = map-modulus-modulated-cauchy-sequence-Metric-Space M x ε⁺
      mδ = map-modulus-modulated-cauchy-sequence-Metric-Space M x δ⁺
      xmε = sequence-modulated-cauchy-sequence-Metric-Space M x mε
      xmδ = sequence-modulated-cauchy-sequence-Metric-Space M x mδ
    in
      rec-coproduct
        ( λ mε≤mδ →
          monotonic-neighborhood-Metric-Space
            ( M)
            ( xmε)
            ( xmδ)
            ( ε⁺)
            ( ε⁺ +ℚ⁺ δ⁺)
            ( le-right-add-rational-ℚ⁺ ε δ⁺)
            ( neighborhood-at-map-modulus-modulated-cauchy-sequence-Metric-Space
              ( M)
              ( x)
              ( ε⁺)
              ( mδ)
              ( mε≤mδ)))
        ( λ mδ≤mε →
          monotonic-neighborhood-Metric-Space
            ( M)
            ( xmε)
            ( xmδ)
            ( δ⁺)
            ( ε⁺ +ℚ⁺ δ⁺)
            ( le-left-add-rational-ℚ⁺ δ ε⁺)
            ( symmetric-neighborhood-Metric-Space
              ( M)
              ( δ⁺)
              ( xmδ)
              ( xmε)
              ( neighborhood-at-map-modulus-modulated-cauchy-sequence-Metric-Space
                ( M)
                ( x)
                ( δ⁺)
                ( mε)
                ( mδ≤mε))))
        ( linear-leq-ℕ mε mδ)

  cauchy-approximation-modulated-cauchy-sequence-Metric-Space :
    cauchy-approximation-Metric-Space M
  pr1 cauchy-approximation-modulated-cauchy-sequence-Metric-Space =
    map-cauchy-approximation-modulated-cauchy-sequence-Metric-Space
  pr2 cauchy-approximation-modulated-cauchy-sequence-Metric-Space =
    is-cauchy-approximation-map-cauchy-approximation-modulated-cauchy-sequence-Metric-Space
```

### Correspondence of Cauchy approximations to Cauchy sequences

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x : cauchy-approximation-Metric-Space M)
  where

  seq-modulated-cauchy-sequence-cauchy-approximation-Metric-Space :
    ℕ → type-Metric-Space M
  seq-modulated-cauchy-sequence-cauchy-approximation-Metric-Space n =
    map-cauchy-approximation-Metric-Space
      ( M)
      ( x)
      ( positive-reciprocal-rational-succ-ℕ n)

  modulus-of-convergence-modulated-cauchy-sequence-cauchy-approximation-Metric-Space :
    ℚ⁺ → ℕ
  modulus-of-convergence-modulated-cauchy-sequence-cauchy-approximation-Metric-Space
    ε⁺ =
    pred-nonzero-ℕ (pr1 (smaller-reciprocal-ℚ⁺ ε⁺))

  abstract
    cauchy-modulus-seq-modulated-cauchy-sequence-cauchy-approximation-Metric-Space :
      cauchy-modulus-sequence-Metric-Space
        ( M)
        ( seq-modulated-cauchy-sequence-cauchy-approximation-Metric-Space)
    cauchy-modulus-seq-modulated-cauchy-sequence-cauchy-approximation-Metric-Space
      ε⁺@(ε , _) =
      let
        (ε'⁺@(ε' , _) , 2ε'<ε) = bound-double-le-ℚ⁺ ε⁺
        (n' , 1/n'<ε') = smaller-reciprocal-ℚ⁺ ε'⁺
        n = pred-nonzero-ℕ n'
        1/n' = positive-reciprocal-rational-ℕ⁺ n'
        xn =
          seq-modulated-cauchy-sequence-cauchy-approximation-Metric-Space n
      in
        n ,
        λ m k n≤m n≤k →
          let
            xm =
              seq-modulated-cauchy-sequence-cauchy-approximation-Metric-Space m
            xk =
              seq-modulated-cauchy-sequence-cauchy-approximation-Metric-Space k
            m' = succ-nonzero-ℕ' m
            k' = succ-nonzero-ℕ' k
            1/m' = positive-reciprocal-rational-ℕ⁺ m'
            1/k' = positive-reciprocal-rational-ℕ⁺ k'
          in
            monotonic-neighborhood-Metric-Space
              ( M)
              ( xm)
              ( xk)
              ( 1/m' +ℚ⁺ 1/k')
              ( ε⁺)
              ( concatenate-leq-le-ℚ
                ( rational-ℚ⁺ (1/m' +ℚ⁺ 1/k'))
                ( rational-ℚ⁺ (1/n' +ℚ⁺ 1/n'))
                ( ε)
                ( preserves-leq-add-ℚ
                  { rational-ℚ⁺ 1/m'}
                  { rational-ℚ⁺ 1/n'}
                  { rational-ℚ⁺ 1/k'}
                  { rational-ℚ⁺ 1/n'}
                  ( leq-reciprocal-rational-ℕ⁺
                    ( n')
                    ( m')
                    ( tr
                      ( λ p → leq-ℕ⁺ p m')
                      ( is-section-succ-nonzero-ℕ' n')
                      ( n≤m)))
                  ( leq-reciprocal-rational-ℕ⁺
                    ( n')
                    ( k')
                    ( tr
                      ( λ p → leq-ℕ⁺ p k')
                      ( is-section-succ-nonzero-ℕ' n')
                      ( n≤k))))
                ( transitive-le-ℚ
                  ( rational-ℚ⁺ (1/n' +ℚ⁺ 1/n'))
                  ( ε' +ℚ ε')
                  ( ε)
                  ( 2ε'<ε)
                  ( preserves-le-add-ℚ
                    { rational-ℚ⁺ 1/n'}
                    { ε'}
                    { rational-ℚ⁺ 1/n'}
                    { ε'}
                    ( 1/n'<ε')
                    ( 1/n'<ε'))))
              ( is-cauchy-approximation-map-cauchy-approximation-Metric-Space
                ( M)
                ( x)
                ( 1/m')
                ( 1/k'))

  modulated-cauchy-sequence-cauchy-approximation-Metric-Space :
    modulated-cauchy-sequence-Metric-Space M
  modulated-cauchy-sequence-cauchy-approximation-Metric-Space =
    ( seq-modulated-cauchy-sequence-cauchy-approximation-Metric-Space ,
      cauchy-modulus-seq-modulated-cauchy-sequence-cauchy-approximation-Metric-Space)
```

### Pairing of modulated Cauchy sequences

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  (u : modulated-cauchy-sequence-Metric-Space A)
  (v : modulated-cauchy-sequence-Metric-Space B)
  where

  seq-pair-modulated-cauchy-sequence-Metric-Space :
    sequence-type-Metric-Space (product-Metric-Space A B)
  seq-pair-modulated-cauchy-sequence-Metric-Space =
    pair-sequence
      ( sequence-modulated-cauchy-sequence-Metric-Space A u)
      ( sequence-modulated-cauchy-sequence-Metric-Space B v)

  abstract
    is-cauchy-seq-pair-modulated-cauchy-sequence-Metric-Space :
      cauchy-modulus-sequence-Metric-Space
        ( product-Metric-Space A B)
        ( seq-pair-modulated-cauchy-sequence-Metric-Space)
    is-cauchy-seq-pair-modulated-cauchy-sequence-Metric-Space ε =
      ( max-ℕ
        ( map-modulus-modulated-cauchy-sequence-Metric-Space A u ε)
        ( map-modulus-modulated-cauchy-sequence-Metric-Space B v ε) ,
        λ m n N≤m N≤n →
          ( neighborhood-map-modulus-modulated-cauchy-sequence-Metric-Space
              ( A)
              ( u)
              ( ε)
              ( m)
              ( n)
              ( transitive-leq-ℕ _ _ _ N≤m (left-leq-max-ℕ _ _))
              ( transitive-leq-ℕ _ _ _ N≤n (left-leq-max-ℕ _ _)) ,
            neighborhood-map-modulus-modulated-cauchy-sequence-Metric-Space
              ( B)
              ( v)
              ( ε)
              ( m)
              ( n)
              ( transitive-leq-ℕ _ _ _ N≤m (right-leq-max-ℕ _ _))
              ( transitive-leq-ℕ _ _ _ N≤n (right-leq-max-ℕ _ _))))

  pair-modulated-cauchy-sequence-Metric-Space :
    modulated-cauchy-sequence-Metric-Space (product-Metric-Space A B)
  pair-modulated-cauchy-sequence-Metric-Space =
    ( seq-pair-modulated-cauchy-sequence-Metric-Space ,
      is-cauchy-seq-pair-modulated-cauchy-sequence-Metric-Space)
```

### To have a Cauchy modulus for a sequence `a`, it suffices to have a modulus function `μ` such that for any `ε`, `a (μ ε)` and `a (μ ε + k)` are in an `ε`-neighborhood

```agda
module
  _
  {l1 l2 : Level}
  (X : Metric-Space l1 l2)
  (a : sequence-type-Metric-Space X)
  (μ : ℚ⁺ → ℕ)
  where

  abstract
    is-cauchy-modulus-neighborhood-add-sequence-Metric-Space :
      ( (ε : ℚ⁺) (k : ℕ) →
        neighborhood-Metric-Space X ε (a (μ ε)) (a (μ ε +ℕ k))) →
      (ε : ℚ⁺) →
      is-cauchy-modulus-sequence-Metric-Space
        ( X)
        ( a)
        ( ε)
        ( μ (pr1 (bound-double-le-ℚ⁺ ε)))
    is-cauchy-modulus-neighborhood-add-sequence-Metric-Space
      H ε p q με'≤p με'≤q =
      let
        (ε' , ε'+ε'<ε) = bound-double-le-ℚ⁺ ε
        (k , k+με'=p) = subtraction-leq-ℕ (μ ε') p με'≤p
        (l , l+με'=q) = subtraction-leq-ℕ (μ ε') q με'≤q
      in
        monotonic-neighborhood-Metric-Space
          ( X)
          ( a p)
          ( a q)
          ( ε' +ℚ⁺ ε')
          ( ε)
          ( ε'+ε'<ε)
          ( triangular-neighborhood-Metric-Space
            ( X)
            ( a p)
            ( a (μ ε'))
            ( a q)
            ( ε')
            ( ε')
            ( tr
              ( λ n → neighborhood-Metric-Space X ε' (a (μ ε')) (a n))
              ( commutative-add-ℕ (μ ε') l ∙ l+με'=q)
              ( H ε' l))
            ( tr
              ( λ n → neighborhood-Metric-Space X ε' (a n) (a (μ ε')))
              ( commutative-add-ℕ (μ ε') k ∙ k+με'=p)
              ( symmetric-neighborhood-Metric-Space X ε' _ _ (H ε' k))))

    cauchy-modulus-neighborhood-add-sequence-Metric-Space :
      ( (ε : ℚ⁺) (k : ℕ) →
        neighborhood-Metric-Space X ε (a (μ ε)) (a (μ ε +ℕ k))) →
      cauchy-modulus-sequence-Metric-Space X a
    cauchy-modulus-neighborhood-add-sequence-Metric-Space H ε =
      ( _ , is-cauchy-modulus-neighborhood-add-sequence-Metric-Space H ε)

  modulated-cauchy-sequence-modulus-neighborhood-add-sequence-Metric-Space :
    ( (ε : ℚ⁺) (k : ℕ) →
      neighborhood-Metric-Space X ε (a (μ ε)) (a (μ ε +ℕ k))) →
    modulated-cauchy-sequence-Metric-Space X
  modulated-cauchy-sequence-modulus-neighborhood-add-sequence-Metric-Space H =
    ( a , cauchy-modulus-neighborhood-add-sequence-Metric-Space H)
```

## See also

- [Cauchy sequences in metric spaces](metric-spaces.cauchy-sequences-metric-spaces.md)
- [Cauchy sequences in complete metric spaces](metric-spaces.cauchy-sequences-complete-metric-spaces.md)

## References

{{#bibliography}}
