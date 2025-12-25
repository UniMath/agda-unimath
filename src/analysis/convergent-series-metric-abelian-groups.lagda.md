# Convergent series in metric abelian groups

```agda
module analysis.convergent-series-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-abelian-groups
open import analysis.series-metric-abelian-groups

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.convergent-sequences-metric-spaces
open import metric-spaces.limits-of-sequences-metric-spaces
```

</details>

## Idea

A [series](analysis.series-metric-abelian-groups.md) in a
[metric abelian group](analysis.metric-abelian-groups.md) is
{{#concept "convergent" Disambiguation="series in a metric abelian group" Agda=is-convergent-series-Metric-Ab Agda=convergent-series-Metric-Ab WDID=Q1211057 WD="convergent series"}}
if its [sequence](lists.sequences.md) of partial sums
[converges](metric-spaces.convergent-sequences-metric-spaces.md) in the
associated [metric space](metric-spaces.metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level} {G : Metric-Ab l1 l2} (σ : series-Metric-Ab G)
  where

  is-sum-prop-series-Metric-Ab : type-Metric-Ab G → Prop l2
  is-sum-prop-series-Metric-Ab =
    is-limit-prop-sequence-Metric-Space
      ( metric-space-Metric-Ab G)
      ( partial-sum-series-Metric-Ab σ)

  is-sum-series-Metric-Ab : type-Metric-Ab G → UU l2
  is-sum-series-Metric-Ab s = type-Prop (is-sum-prop-series-Metric-Ab s)

  is-convergent-prop-series-Metric-Ab : Prop (l1 ⊔ l2)
  is-convergent-prop-series-Metric-Ab =
    subtype-convergent-sequence-Metric-Space
      ( metric-space-Metric-Ab G)
      ( partial-sum-series-Metric-Ab σ)

  is-convergent-series-Metric-Ab : UU (l1 ⊔ l2)
  is-convergent-series-Metric-Ab =
    type-Prop is-convergent-prop-series-Metric-Ab

convergent-series-Metric-Ab :
  {l1 l2 : Level} (G : Metric-Ab l1 l2) → UU (l1 ⊔ l2)
convergent-series-Metric-Ab G =
  type-subtype (is-convergent-prop-series-Metric-Ab {G = G})
```

## Properties

```agda
module _
  {l1 l2 : Level} (G : Metric-Ab l1 l2) (σ : convergent-series-Metric-Ab G)
  where

  series-convergent-series-Metric-Ab : series-Metric-Ab G
  series-convergent-series-Metric-Ab = pr1 σ

  partial-sum-convergent-series-Metric-Ab : sequence (type-Metric-Ab G)
  partial-sum-convergent-series-Metric-Ab =
    partial-sum-series-Metric-Ab series-convergent-series-Metric-Ab
```

### The partial sums of a convergent series have a limit, the sum of the series

```agda
module _
  {l1 l2 : Level} (G : Metric-Ab l1 l2) (σ : convergent-series-Metric-Ab G)
  where

  has-limit-partial-sum-convergent-series-Metric-Ab :
    has-limit-sequence-Metric-Space
      ( metric-space-Metric-Ab G)
      ( partial-sum-convergent-series-Metric-Ab G σ)
  has-limit-partial-sum-convergent-series-Metric-Ab =
    pr2 σ

  sum-convergent-series-Metric-Ab : type-Metric-Ab G
  sum-convergent-series-Metric-Ab =
    limit-has-limit-sequence-Metric-Space
      ( metric-space-Metric-Ab G)
      ( partial-sum-convergent-series-Metric-Ab G σ)
      ( has-limit-partial-sum-convergent-series-Metric-Ab)

  is-limit-partial-sum-convergent-series-Metric-Ab :
    is-limit-sequence-Metric-Space
      ( metric-space-Metric-Ab G)
      ( partial-sum-convergent-series-Metric-Ab G σ)
      ( sum-convergent-series-Metric-Ab)
  is-limit-partial-sum-convergent-series-Metric-Ab =
    is-limit-limit-has-limit-sequence-Metric-Space
      ( metric-space-Metric-Ab G)
      ( partial-sum-convergent-series-Metric-Ab G σ)
      ( has-limit-partial-sum-convergent-series-Metric-Ab)
```

### A series converges if and only if it converges after dropping a finite number of terms

```agda
module _
  {l1 l2 : Level}
  {G : Metric-Ab l1 l2}
  (σ : series-Metric-Ab G)
  (k : ℕ)
  where

  is-convergent-is-convergent-drop-series-ℝ :
    is-convergent-series-Metric-Ab (drop-series-Metric-Ab k σ) →
    is-convergent-series-Metric-Ab σ
  is-convergent-is-convergent-drop-series-ℝ (lim-drop , is-lim-drop) =
    ( add-Metric-Ab G (partial-sum-series-Metric-Ab σ k) lim-drop ,
      map-trunc-Prop
        ( λ (μ , is-mod-μ) →
          ( ( λ ε → μ ε +ℕ k) ,
            ( λ ε n με+k≤n →
              let
                (l , l+k=n) =
                  subtraction-leq-ℕ
                    ( k)
                    ( n)
                    ( transitive-leq-ℕ
                      ( k)
                      ( μ ε +ℕ k)
                      ( n)
                      ( με+k≤n)
                      ( leq-add-ℕ' k (μ ε)))
              in
                tr
                  ( λ x → neighborhood-Metric-Ab G ε x _)
                  ( equational-reasoning
                    add-Metric-Ab G
                      ( partial-sum-series-Metric-Ab σ k)
                      ( partial-sum-series-Metric-Ab
                        ( drop-series-Metric-Ab k σ)
                        ( l))
                    ＝
                      add-Metric-Ab G
                        ( partial-sum-series-Metric-Ab σ k)
                        ( diff-Metric-Ab G
                          ( partial-sum-series-Metric-Ab σ (k +ℕ l))
                          ( partial-sum-series-Metric-Ab σ k))
                      by
                        ap-add-Metric-Ab G
                          ( refl)
                          ( partial-sum-drop-series-Metric-Ab k σ l)
                    ＝ partial-sum-series-Metric-Ab σ (k +ℕ l)
                      by is-identity-right-conjugation-Metric-Ab G _ _
                    ＝ partial-sum-series-Metric-Ab σ n
                      by
                        ap
                          ( partial-sum-series-Metric-Ab σ)
                          ( commutative-add-ℕ k l ∙ l+k=n))
                  ( forward-implication
                    ( is-isometry-add-Metric-Ab
                      ( G)
                      ( partial-sum-series-Metric-Ab σ k)
                      ( ε)
                      ( partial-sum-series-Metric-Ab
                        ( drop-series-Metric-Ab k σ)
                        ( l))
                      ( lim-drop))
                      ( is-mod-μ
                        ( ε)
                        ( l)
                        ( reflects-leq-left-add-ℕ
                          ( k)
                          ( μ ε)
                          ( l)
                          ( inv-tr (leq-ℕ (μ ε +ℕ k)) l+k=n με+k≤n)))))))
        ( is-lim-drop))
```
