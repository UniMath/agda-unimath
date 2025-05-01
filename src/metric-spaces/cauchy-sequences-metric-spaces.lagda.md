# Cauchy sequences in metric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.cauchy-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.archimedean-property-positive-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sequences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.convergent-sequences-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-premetric-spaces
open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.sequences-metric-spaces
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

A
{{#concept "Cauchy sequence" Disambiguation="in a metric space" WD="cauchy sequence" WDID=Q217847 Agda=is-cauchy-sequence-Metric-Space}}
`x` in a [metric space](metric-spaces.metric-spaces.md) is a mapping from the
[natural numbers](elementary-number-theory.natural-numbers.md) to the underlying
type of the metric space such that for any
[positive rational](elementary-number-theory.positive-rational-numbers.md) `ε`,
there is a concrete `n : ℕ` such that for any `m, k ≥ n`, `x m` and `x k` are in
an `ε`-neighborhood of each other.

Importantly, this is a structure, not a proposition, allowing us to explicitly
calculate rates of convergence. This follows Section 11.2.2 in {{#cite UF13}}.

In a metric space, every Cauchy sequence has a (non-unique) corresponding Cauchy
approximation, with the same limit if either exists, and vice versa.

## Definition

### Cauchy sequences

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x : sequence-type-Metric-Space M)
  where

  is-cauchy-modulus-sequence-Metric-Space : ℚ⁺ → ℕ → UU l2
  is-cauchy-modulus-sequence-Metric-Space ε N =
    (m k : ℕ) → leq-ℕ N m → leq-ℕ N k →
    neighborhood-Metric-Space M ε (x m) (x k)

  is-cauchy-sequence-Metric-Space : UU l2
  is-cauchy-sequence-Metric-Space =
    (ε : ℚ⁺) → Σ ℕ (is-cauchy-modulus-sequence-Metric-Space ε)

module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  cauchy-sequence-Metric-Space : UU (l1 ⊔ l2)
  cauchy-sequence-Metric-Space =
    Σ (sequence-type-Metric-Space M) (is-cauchy-sequence-Metric-Space M)

  modulus-of-convergence-cauchy-sequence-Metric-Space :
    cauchy-sequence-Metric-Space → ℚ⁺ → ℕ
  modulus-of-convergence-cauchy-sequence-Metric-Space (x , is-cauchy-x) ε⁺ =
    pr1 (is-cauchy-x ε⁺)

  map-cauchy-sequence-Metric-Space :
    cauchy-sequence-Metric-Space → sequence-type-Metric-Space M
  map-cauchy-sequence-Metric-Space = pr1

  is-cauchy-sequence-cauchy-sequence-Metric-Space :
    (x : cauchy-sequence-Metric-Space) →
    is-cauchy-sequence-Metric-Space M (map-cauchy-sequence-Metric-Space x)
  is-cauchy-sequence-cauchy-sequence-Metric-Space = pr2

  neighborhood-modulus-of-convergence-cauchy-sequence-Metric-Space :
    (x : cauchy-sequence-Metric-Space) (ε⁺ : ℚ⁺) (m k : ℕ) →
    leq-ℕ (modulus-of-convergence-cauchy-sequence-Metric-Space x ε⁺) m →
    leq-ℕ (modulus-of-convergence-cauchy-sequence-Metric-Space x ε⁺) k →
    neighborhood-Metric-Space
      ( M)
      ( ε⁺)
      ( map-cauchy-sequence-Metric-Space x m)
      ( map-cauchy-sequence-Metric-Space x k)
  neighborhood-modulus-of-convergence-cauchy-sequence-Metric-Space
    (x , is-cauchy-x) ε⁺ = pr2 (is-cauchy-x ε⁺)

  map-at-modulus-of-convergence-cauchy-sequence-Metric-Space :
    (x : cauchy-sequence-Metric-Space) (ε⁺ : ℚ⁺) → type-Metric-Space M
  map-at-modulus-of-convergence-cauchy-sequence-Metric-Space x ε⁺ =
    map-cauchy-sequence-Metric-Space
      ( x)
      ( modulus-of-convergence-cauchy-sequence-Metric-Space x ε⁺)

  neighborhood-at-modulus-of-convergence-cauchy-sequence-Metric-Space :
    (x : cauchy-sequence-Metric-Space) (ε⁺ : ℚ⁺) (m : ℕ) →
    leq-ℕ (modulus-of-convergence-cauchy-sequence-Metric-Space x ε⁺) m →
    neighborhood-Metric-Space
      ( M)
      ( ε⁺)
      ( map-at-modulus-of-convergence-cauchy-sequence-Metric-Space x ε⁺)
      ( map-cauchy-sequence-Metric-Space x m)
  neighborhood-at-modulus-of-convergence-cauchy-sequence-Metric-Space
    x ε⁺ m n≤m =
    let
      n = modulus-of-convergence-cauchy-sequence-Metric-Space x ε⁺
    in
      neighborhood-modulus-of-convergence-cauchy-sequence-Metric-Space
        ( x)
        ( ε⁺)
        ( n)
        ( m)
        ( refl-leq-ℕ n)
        ( n≤m)
```

### Limits of Cauchy sequences

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x : cauchy-sequence-Metric-Space M)
  (lim : type-Metric-Space M)
  where

  is-limit-cauchy-sequence-Metric-Space : UU l2
  is-limit-cauchy-sequence-Metric-Space =
    is-limit-sequence-Metric-Space
      ( M)
      ( map-cauchy-sequence-Metric-Space M x)
      ( lim)

module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x : cauchy-sequence-Metric-Space M)
  where

  has-limit-cauchy-sequence-Metric-Space : UU (l1 ⊔ l2)
  has-limit-cauchy-sequence-Metric-Space =
    Σ (type-Metric-Space M) (is-limit-cauchy-sequence-Metric-Space M x)
```

## Properties

### A sequence with a convergence modulus is Cauchy

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x : sequence-type-Metric-Space M)
  (lim : type-Metric-Space M)
  (H : limit-modulus-sequence-Metric-Space M x lim)
  where

  is-cauchy-has-limit-modulus-sequence-Metric-Space :
    is-cauchy-sequence-Metric-Space M x
  is-cauchy-has-limit-modulus-sequence-Metric-Space ε⁺@(ε , _) =
      let
        (ε'⁺@(ε' , _) , 2ε'<ε) = bound-double-le-ℚ⁺ ε⁺
      in
        modulus-limit-modulus-sequence-Metric-Space M x lim H ε'⁺ ,
        λ m k n≤m n≤k →
        is-monotonic-structure-Metric-Space
          ( M)
          ( x m)
          ( x k)
          ( ε'⁺ +ℚ⁺ ε'⁺)
          ( ε⁺)
          ( 2ε'<ε)
          ( is-triangular-structure-Metric-Space
            ( M)
            ( x m)
            ( lim)
            ( x k)
            ( ε'⁺)
            ( ε'⁺)
            ( is-symmetric-structure-Metric-Space
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
              ( n≤m)))
```

### Correspondence to Cauchy approximations

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x : cauchy-sequence-Metric-Space M)
  where

  map-cauchy-approximation-cauchy-sequence-Metric-Space :
    ℚ⁺ → type-Metric-Space M
  map-cauchy-approximation-cauchy-sequence-Metric-Space ε =
    map-cauchy-sequence-Metric-Space
      ( M)
      ( x)
      ( modulus-of-convergence-cauchy-sequence-Metric-Space M x ε)

  abstract
    is-cauchy-approximation-cauchy-approximation-cauchy-sequence-Metric-Space :
      is-cauchy-approximation-Metric-Space
        ( M)
        ( map-cauchy-approximation-cauchy-sequence-Metric-Space)
    is-cauchy-approximation-cauchy-approximation-cauchy-sequence-Metric-Space
      ε⁺@(ε , _) δ⁺@(δ , _) =
        let
          mε = modulus-of-convergence-cauchy-sequence-Metric-Space M x ε⁺
          mδ = modulus-of-convergence-cauchy-sequence-Metric-Space M x δ⁺
          xmε = map-cauchy-sequence-Metric-Space M x mε
          xmδ = map-cauchy-sequence-Metric-Space M x mδ
        in
          rec-coproduct
            ( λ mε≤mδ →
              is-monotonic-structure-Metric-Space
                ( M)
                ( xmε)
                ( xmδ)
                ( ε⁺)
                ( ε⁺ +ℚ⁺ δ⁺)
                ( le-right-add-rational-ℚ⁺ ε δ⁺)
                ( neighborhood-at-modulus-of-convergence-cauchy-sequence-Metric-Space
                  ( M)
                  ( x)
                  ( ε⁺)
                  ( mδ)
                  ( mε≤mδ)))
            ( λ mδ≤mε →
              is-monotonic-structure-Metric-Space
                ( M)
                ( xmε)
                ( xmδ)
                ( δ⁺)
                ( ε⁺ +ℚ⁺ δ⁺)
                ( le-left-add-rational-ℚ⁺ δ ε⁺)
                ( is-symmetric-structure-Metric-Space
                  ( M)
                  ( δ⁺)
                  ( xmδ)
                  ( xmε)
                  ( neighborhood-at-modulus-of-convergence-cauchy-sequence-Metric-Space
                    ( M)
                    ( x)
                    ( δ⁺)
                    ( mε)
                    ( mδ≤mε))))
            ( linear-leq-ℕ mε mδ)

  cauchy-approximation-cauchy-sequence-Metric-Space :
    cauchy-approximation-Metric-Space M
  pr1 cauchy-approximation-cauchy-sequence-Metric-Space =
    map-cauchy-approximation-cauchy-sequence-Metric-Space
  pr2 cauchy-approximation-cauchy-sequence-Metric-Space =
    is-cauchy-approximation-cauchy-approximation-cauchy-sequence-Metric-Space
```

### The limit of a Cauchy approximation corresponding to a Cauchy sequence is the limit of the sequence

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x : cauchy-sequence-Metric-Space M)
  (lim : type-Metric-Space M)
  (H :
    is-limit-cauchy-approximation-Premetric-Space
      ( premetric-Metric-Space M)
      ( cauchy-approximation-cauchy-sequence-Metric-Space M x)
      ( lim))
  where

  modulus-cauchy-sequence-limit-cauchy-approximation-cauchy-sequence-Metric-Space :
    ℚ⁺ → ℕ
  modulus-cauchy-sequence-limit-cauchy-approximation-cauchy-sequence-Metric-Space
    ε⁺@(ε , _) =
      let
        (ε'⁺@(ε' , _) , 2ε'<ε) = bound-double-le-ℚ⁺ ε⁺
        ε''⁺@(ε'' , _) = left-summand-split-ℚ⁺ ε'⁺
      in
        modulus-of-convergence-cauchy-sequence-Metric-Space M x ε''⁺

  is-limit-modulus-cauchy-sequence-limit-cauchy-approximation-cauchy-sequence-Metric-Space :
    is-limit-modulus-sequence-Metric-Space
      ( M)
      ( map-cauchy-sequence-Metric-Space M x)
      ( lim)
      ( modulus-cauchy-sequence-limit-cauchy-approximation-cauchy-sequence-Metric-Space)
  is-limit-modulus-cauchy-sequence-limit-cauchy-approximation-cauchy-sequence-Metric-Space
    ε⁺@(ε , _) m n≤m =
    let
      (ε'⁺@(ε' , _) , 2ε'<ε) = bound-double-le-ℚ⁺ ε⁺
      ε''⁺@(ε'' , _) = left-summand-split-ℚ⁺ ε'⁺
      n =
        modulus-of-convergence-cauchy-sequence-Metric-Space M x ε''⁺
      xn = map-cauchy-sequence-Metric-Space M x n
      xm = map-cauchy-sequence-Metric-Space M x m
    in
      is-monotonic-structure-Metric-Space
        ( M)
        ( xm)
        ( lim)
        ( ε''⁺ +ℚ⁺ ε'⁺)
        ( ε⁺)
        ( transitive-le-ℚ
          ( ε'' +ℚ ε')
          ( ε' +ℚ ε')
          ( ε)
          ( 2ε'<ε)
          ( preserves-le-left-add-ℚ ε' ε'' ε' (le-mediant-zero-ℚ⁺ ε'⁺)))
        ( is-triangular-structure-Metric-Space
          ( M)
          ( xm)
          ( xn)
          ( lim)
          ( ε''⁺)
          ( ε'⁺)
          ( tr
            ( λ d → neighborhood-Metric-Space M d xn lim)
            ( eq-add-split-ℚ⁺ ε'⁺)
            ( H ε''⁺ (right-summand-split-ℚ⁺ ε'⁺)))
          ( is-symmetric-structure-Metric-Space
            ( M)
            ( ε''⁺)
            ( xn)
            ( xm)
            ( neighborhood-at-modulus-of-convergence-cauchy-sequence-Metric-Space
              ( M)
              ( x)
              ( ε''⁺)
              ( m)
              ( n≤m))))

  abstract
    is-limit-cauchy-sequence-limit-cauchy-approximation-cauchy-sequence-Metric-Space :
      is-limit-cauchy-sequence-Metric-Space M x lim
    is-limit-cauchy-sequence-limit-cauchy-approximation-cauchy-sequence-Metric-Space =
        unit-trunc-Prop
          ( modulus-cauchy-sequence-limit-cauchy-approximation-cauchy-sequence-Metric-Space ,
            is-limit-modulus-cauchy-sequence-limit-cauchy-approximation-cauchy-sequence-Metric-Space)
```

### Correspondence of Cauchy approximations to Cauchy sequences

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x : cauchy-approximation-Metric-Space M)
  where

  map-cauchy-sequence-cauchy-approximation-Metric-Space :
    ℕ → type-Metric-Space M
  map-cauchy-sequence-cauchy-approximation-Metric-Space n =
    map-cauchy-approximation-Metric-Space
      ( M)
      ( x)
      ( positive-reciprocal-rational-ℕ⁺ (succ-nonzero-ℕ' n))

  modulus-of-convergence-cauchy-sequence-cauchy-approximation-Metric-Space :
    ℚ⁺ → ℕ
  modulus-of-convergence-cauchy-sequence-cauchy-approximation-Metric-Space ε⁺ =
    pred-nonzero-ℕ (pr1 (smaller-reciprocal-ℚ⁺ ε⁺))

  abstract
    is-cauchy-sequence-cauchy-sequence-cauchy-approximation-Metric-Space :
      is-cauchy-sequence-Metric-Space
        ( M)
        ( map-cauchy-sequence-cauchy-approximation-Metric-Space)
    is-cauchy-sequence-cauchy-sequence-cauchy-approximation-Metric-Space
      ε⁺@(ε , _) =
      let
        (ε'⁺@(ε' , _) , 2ε'<ε) = bound-double-le-ℚ⁺ ε⁺
        (n' , 1/n'<ε') = smaller-reciprocal-ℚ⁺ ε'⁺
        n = pred-nonzero-ℕ n'
        1/n' = positive-reciprocal-rational-ℕ⁺ n'
        xn = map-cauchy-sequence-cauchy-approximation-Metric-Space n
      in
        n ,
        λ m k n≤m n≤k →
          let
            xm = map-cauchy-sequence-cauchy-approximation-Metric-Space m
            xk = map-cauchy-sequence-cauchy-approximation-Metric-Space k
            m' = succ-nonzero-ℕ' m
            k' = succ-nonzero-ℕ' k
            1/m' = positive-reciprocal-rational-ℕ⁺ m'
            1/k' = positive-reciprocal-rational-ℕ⁺ k'
          in
            is-monotonic-structure-Metric-Space
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

  cauchy-sequence-cauchy-approximation-Metric-Space :
    cauchy-sequence-Metric-Space M
  cauchy-sequence-cauchy-approximation-Metric-Space =
    map-cauchy-sequence-cauchy-approximation-Metric-Space ,
    is-cauchy-sequence-cauchy-sequence-cauchy-approximation-Metric-Space
```

### If the Cauchy sequence associated with a Cauchy approximation has a limit modulus at `l`, its associated approximation converges to `l`

```agda
module _
  { l1 l2 : Level} (M : Metric-Space l1 l2)
  ( x : cauchy-approximation-Metric-Space M)
  ( l : type-Metric-Space M)
  ( H :
    limit-modulus-sequence-Metric-Space
      ( M)
      ( map-cauchy-sequence-Metric-Space
        ( M)
        ( cauchy-sequence-cauchy-approximation-Metric-Space M x))
      ( l))
  where

  abstract
    is-limit-cauchy-approximation-limit-modulus-cauchy-sequence-cauchy-approximation-Metric-Space :
      is-limit-cauchy-approximation-Premetric-Space
        ( premetric-Metric-Space M)
        ( x)
        ( l)
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
          ( l)
          ( H)
          ( δ'⁺)
        n = max-ℕ n₁ n₂
        n' = succ-nonzero-ℕ' n
        1/n' = positive-reciprocal-rational-ℕ⁺ n'
        xε = map-cauchy-approximation-Metric-Space M x ε⁺
        x1/n' = map-cauchy-approximation-Metric-Space M x 1/n'
        x1/n'-l-neighborhood :
          neighborhood-Metric-Space M δ'⁺ x1/n' l
        x1/n'-l-neighborhood =
          is-modulus-limit-modulus-sequence-Metric-Space
            ( M)
            ( map-cauchy-sequence-Metric-Space
              ( M)
              ( cauchy-sequence-cauchy-approximation-Metric-Space M x))
            ( l)
            ( H)
            ( δ'⁺)
            ( n)
            ( right-leq-max-ℕ n₁ n₂)
      in
        is-monotonic-structure-Metric-Space
          ( M)
          ( xε)
          ( l)
          ( (ε⁺ +ℚ⁺ δ'⁺) +ℚ⁺ δ'⁺)
          ( ε⁺ +ℚ⁺ δ⁺)
          ( inv-tr
            ( λ y → le-ℚ⁺ y (ε⁺ +ℚ⁺ δ⁺))
            ( associative-add-ℚ⁺ ε⁺ δ'⁺ δ'⁺)
            ( preserves-le-right-add-ℚ ε (δ' +ℚ δ') δ 2δ'<δ))
          ( is-triangular-structure-Metric-Space
            ( M)
            ( xε)
            ( x1/n')
            ( l)
            ( ε⁺ +ℚ⁺ δ'⁺)
            ( δ'⁺)
            ( x1/n'-l-neighborhood)
            ( is-monotonic-structure-Metric-Space
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
  (l : type-Metric-Space M)
  where

  abstract
    is-limit-cauchy-approximation-limit-cauchy-sequence-cauchy-approximation-Metric-Space :
      is-limit-cauchy-sequence-Metric-Space
        ( M)
        ( cauchy-sequence-cauchy-approximation-Metric-Space M x)
        ( l) →
      is-limit-cauchy-approximation-Premetric-Space
        ( premetric-Metric-Space M)
        ( x)
        ( l)
    is-limit-cauchy-approximation-limit-cauchy-sequence-cauchy-approximation-Metric-Space
      =
        rec-trunc-Prop
          ( is-limit-cauchy-approximation-prop-Premetric-Space
            ( premetric-Metric-Space M)
            ( x)
            ( l))
          ( is-limit-cauchy-approximation-limit-modulus-cauchy-sequence-cauchy-approximation-Metric-Space
            ( M)
            ( x)
            ( l))
```

### Short maps between metric spaces preserve Cauchy sequences

```agda
module _
  {l1 l2 l1' l2' : Level} (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : short-function-Metric-Space A B)
  (u : cauchy-sequence-Metric-Space A)
  where

  seq-short-map-cauchy-sequence-Metric-Space : sequence-type-Metric-Space B
  seq-short-map-cauchy-sequence-Metric-Space =
    map-sequence
      ( map-short-function-Metric-Space A B f)
      ( map-cauchy-sequence-Metric-Space A u)

  is-cauchy-seq-short-map-cauchy-sequence-Metric-Space :
    is-cauchy-sequence-Metric-Space B seq-short-map-cauchy-sequence-Metric-Space
  is-cauchy-seq-short-map-cauchy-sequence-Metric-Space ε =
    tot
      ( λ n H m k I J →
        is-short-map-short-function-Metric-Space A B f ε
          ( map-cauchy-sequence-Metric-Space A u m)
          ( map-cauchy-sequence-Metric-Space A u k)
          ( H m k I J))
      ( is-cauchy-sequence-cauchy-sequence-Metric-Space A u ε)

  map-short-map-cauchy-sequence-Metric-Space : cauchy-sequence-Metric-Space B
  map-short-map-cauchy-sequence-Metric-Space =
    seq-short-map-cauchy-sequence-Metric-Space ,
    is-cauchy-seq-short-map-cauchy-sequence-Metric-Space
```

## See also

- [Cauchy sequences in complete metric spaces](metric-spaces.cauchy-sequences-complete-metric-spaces.md)

## External links

- [Cauchy sequences](https://en.wikipedia.org/wiki/Cauchy_sequence) at Wikipedia

## References

{{#bibliography}}
