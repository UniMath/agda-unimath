# Series in metric abelian groups

```agda
module analysis.series-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-abelian-groups

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.sums-of-finite-sequences-of-elements-abelian-groups

open import lists.sequences

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A
{{#concept "series" WD="series" WDID=Q170198 disambiguation="in an abelian group" Agda=series-Metric-Ab}}
in a [metric abelian group](analysis.metric-abelian-groups.md) `G` is a sum over
a countably infinite [sequence](lists.sequences.md) of elements of `G`.

## Definition

Series are defined with a record to make them intensionally distinct from the
sequence of their terms.

```agda
record series-Metric-Ab {l1 l2 : Level} (G : Metric-Ab l1 l2) : UU l1 where
  constructor series-terms-Metric-Ab
  field
    term-series-Metric-Ab : sequence (type-Metric-Ab G)

open series-Metric-Ab public
```

## Properties

### Equality of series

```agda
module _
  {l1 l2 : Level} (G : Metric-Ab l1 l2)
  where

  equiv-series-sequence-Metric-Ab :
    series-Metric-Ab G ≃ sequence (type-Metric-Ab G)
  equiv-series-sequence-Metric-Ab =
    ( term-series-Metric-Ab ,
      is-equiv-is-invertible series-terms-Metric-Ab (λ x → refl) (λ x → refl))

  eq-series-Metric-Ab :
    {f g : series-Metric-Ab G} →
    term-series-Metric-Ab f ＝ term-series-Metric-Ab g → f ＝ g
  eq-series-Metric-Ab = ap series-terms-Metric-Ab

  eq-htpy-term-series-Metric-Ab :
    {f g : series-Metric-Ab G} →
    term-series-Metric-Ab f ~ term-series-Metric-Ab g → f ＝ g
  eq-htpy-term-series-Metric-Ab f~g = eq-series-Metric-Ab (eq-htpy f~g)
```

### Partial sums of a series

```agda
module _
  {l1 l2 : Level} {G : Metric-Ab l1 l2}
  where

  partial-sum-series-Metric-Ab : series-Metric-Ab G → ℕ → type-Metric-Ab G
  partial-sum-series-Metric-Ab (series-terms-Metric-Ab f) n =
    sum-fin-sequence-type-Ab (ab-Metric-Ab G) n (λ i → f (nat-Fin n i))
```

### The `n`th term of a series is the difference of the `succ-ℕ n`th partial sum and the `n`th

```agda
module _
  {l1 l2 : Level} {G : Metric-Ab l1 l2}
  where

  eq-term-diff-partial-sum-series-Metric-Ab :
    (f : series-Metric-Ab G) (n : ℕ) →
    add-Metric-Ab G
      ( partial-sum-series-Metric-Ab f (succ-ℕ n))
      ( neg-Metric-Ab G (partial-sum-series-Metric-Ab f n)) ＝
    term-series-Metric-Ab f n
  eq-term-diff-partial-sum-series-Metric-Ab (series-terms-Metric-Ab f) n =
    ap-add-Metric-Ab G
      ( cons-sum-fin-sequence-type-Ab
        ( ab-Metric-Ab G)
        ( n)
        ( f ∘ nat-Fin (succ-ℕ n)) refl)
      ( refl) ∙
    is-identity-left-conjugation-Ab (ab-Metric-Ab G) _ _
```

### Two series are equal if and only if their partial sums are homotopic

```agda
module _
  {l1 l2 : Level} {G : Metric-Ab l1 l2}
  where

  htpy-htpy-partial-sum-series-Metric-Ab :
    {σ τ : series-Metric-Ab G} →
    (partial-sum-series-Metric-Ab σ ~ partial-sum-series-Metric-Ab τ) →
    term-series-Metric-Ab σ ~ term-series-Metric-Ab τ
  htpy-htpy-partial-sum-series-Metric-Ab {σ} {τ} psσ~psτ n =
    inv (eq-term-diff-partial-sum-series-Metric-Ab σ n) ∙
    ap-right-subtraction-Ab (ab-Metric-Ab G) (psσ~psτ (succ-ℕ n)) (psσ~psτ n) ∙
    eq-term-diff-partial-sum-series-Metric-Ab τ n

  eq-htpy-partial-sum-series-Metric-Ab :
    {σ τ : series-Metric-Ab G} →
    (partial-sum-series-Metric-Ab σ ~ partial-sum-series-Metric-Ab τ) →
    σ ＝ τ
  eq-htpy-partial-sum-series-Metric-Ab psσ~psτ =
    eq-htpy-term-series-Metric-Ab G
      ( htpy-htpy-partial-sum-series-Metric-Ab psσ~psτ)
```

### Dropping terms from a series

```agda
module _
  {l1 l2 : Level} {G : Metric-Ab l1 l2}
  where

  drop-series-Metric-Ab : ℕ → series-Metric-Ab G → series-Metric-Ab G
  drop-series-Metric-Ab n (series-terms-Metric-Ab f) =
    series-terms-Metric-Ab (f ∘ add-ℕ n)
```

### The partial sums of a series after dropping terms

```agda
module _
  {l1 l2 : Level} {G : Metric-Ab l1 l2}
  where

  abstract
    partial-sum-drop-series-Metric-Ab :
      (n : ℕ) (σ : series-Metric-Ab G) (i : ℕ) →
      partial-sum-series-Metric-Ab (drop-series-Metric-Ab n σ) i ＝
      diff-Metric-Ab G
        ( partial-sum-series-Metric-Ab σ (n +ℕ i))
        ( partial-sum-series-Metric-Ab σ n)
    partial-sum-drop-series-Metric-Ab n s@(series-terms-Metric-Ab σ) i =
      inv
        ( equational-reasoning
          diff-Metric-Ab G
            ( partial-sum-series-Metric-Ab s (n +ℕ i))
            ( partial-sum-series-Metric-Ab s n)
          ＝
            diff-Metric-Ab G
              ( add-Metric-Ab G
                ( sum-fin-sequence-type-Ab (ab-Metric-Ab G) n
                  ( σ ∘ nat-Fin (n +ℕ i) ∘ inl-coproduct-Fin n i))
                ( sum-fin-sequence-type-Ab (ab-Metric-Ab G) i
                  ( σ ∘ nat-Fin (n +ℕ i) ∘ inr-coproduct-Fin n i)))
              ( partial-sum-series-Metric-Ab s n)
            by
              ap-diff-Metric-Ab G
                ( split-sum-fin-sequence-type-Ab
                  ( ab-Metric-Ab G)
                  ( n)
                  ( i)
                  ( σ ∘ nat-Fin (n +ℕ i)))
                ( refl)
          ＝
            diff-Metric-Ab G
              ( add-Metric-Ab G
                ( partial-sum-series-Metric-Ab s n)
                ( partial-sum-series-Metric-Ab
                  ( series-terms-Metric-Ab {G = G} (σ ∘ add-ℕ n))
                  ( i)))
              ( partial-sum-series-Metric-Ab s n)
            by
              ap-diff-Metric-Ab G
                ( ap-add-Metric-Ab G
                  ( htpy-sum-fin-sequence-type-Ab (ab-Metric-Ab G) n
                    ( λ j → ap σ (nat-inl-coproduct-Fin n i j)))
                  ( htpy-sum-fin-sequence-type-Ab (ab-Metric-Ab G) i
                    ( λ j → ap σ (nat-inr-coproduct-Fin n i j))))
                ( refl)
          ＝
            partial-sum-series-Metric-Ab
              ( series-terms-Metric-Ab {G = G} (σ ∘ add-ℕ n))
              ( i)
            by is-identity-left-conjugation-Ab (ab-Metric-Ab G) _ _)
```
