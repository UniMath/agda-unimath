# Indicator finite sequences in rings

```agda
module linear-algebra.indicator-finite-sequences-in-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.propositions
open import foundation.singleton-subtypes-discrete-types
open import foundation.universe-levels

open import group-theory.sums-of-finite-families-of-elements-abelian-groups
open import group-theory.sums-of-finite-sequences-of-elements-abelian-groups

open import linear-algebra.dot-product-finite-sequences-in-rings
open import linear-algebra.finite-sequences-in-rings
open import linear-algebra.sums-of-finite-sequences-of-elements-left-modules-rings

open import ring-theory.central-elements-rings
open import ring-theory.rings
open import ring-theory.sums-of-finite-families-of-elements-rings
open import ring-theory.sums-of-finite-sequences-of-elements-rings

open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "indicator finite sequence" Disambiguation="in a ring" Agda=indicator-fin-sequence-type-Ring}}
in a [ring](ring-theory.rings.md) `R` `χᵢ` for index `i : Fin n` is a
[finite sequence](linear-algebra.finite-sequences-in-rings.md) in `R` `u` such
that `uᵢ = 1` and `uⱼ = 0` whenever `j ≠ i`.

## Definition

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  where

  indicator-fin-sequence-type-Ring :
    (i : Fin n) → fin-sequence-type-Ring R n
  indicator-fin-sequence-type-Ring i j =
    rec-coproduct
      ( λ _ → one-Ring R)
      ( λ _ → zero-Ring R)
      ( has-decidable-equality-Fin n i j)

  abstract
    compute-at-index-indicator-fin-sequence-type-Ring :
      (i : Fin n) → indicator-fin-sequence-type-Ring i i ＝ one-Ring R
    compute-at-index-indicator-fin-sequence-type-Ring i =
      ap
        ( rec-coproduct (λ _ → one-Ring R) (λ _ → zero-Ring R))
        ( eq-is-prop'
          ( is-prop-is-decidable (is-set-Fin n i i))
          ( has-decidable-equality-Fin n i i)
          ( inl refl))

    compute-at-other-index-indicator-fin-sequence-type-Ring :
      (i j : Fin n) → i ≠ j →
      indicator-fin-sequence-type-Ring i j ＝ zero-Ring R
    compute-at-other-index-indicator-fin-sequence-type-Ring i j i≠j =
      ap
        ( rec-coproduct (λ _ → one-Ring R) (λ _ → zero-Ring R))
        ( eq-is-prop'
          ( is-prop-is-decidable (is-set-Fin n i j))
          ( has-decidable-equality-Fin n i j)
          ( inr i≠j))
```

## Properties

### `χᵢⱼ = χⱼᵢ`

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  where abstract

  symmetric-indicator-fin-sequence-type-Ring :
    (i j : Fin n) →
    indicator-fin-sequence-type-Ring R n i j ＝
    indicator-fin-sequence-type-Ring R n j i
  symmetric-indicator-fin-sequence-type-Ring i j
    with has-decidable-equality-Fin n i j
  ... | inl i=j =
    ap
      ( rec-coproduct (λ _ → one-Ring R) (λ _ → zero-Ring R))
      ( eq-is-prop'
        ( is-prop-is-decidable (is-set-Fin n j i))
        ( inl (inv i=j))
        ( has-decidable-equality-Fin n j i))
  ... | inr i≠j =
    ap
      ( rec-coproduct (λ _ → one-Ring R) (λ _ → zero-Ring R))
      ( eq-is-prop'
        ( is-prop-is-decidable (is-set-Fin n j i))
        ( inr (is-symmetric-nonequal i j i≠j))
        ( has-decidable-equality-Fin n j i))
```

### Every coordinate of an indicator sequence at an index `i` is central

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  (i : Fin n)
  where abstract

  is-central-element-indicator-fin-sequence-type-Ring :
    (j : Fin n) →
    is-central-element-Ring R (indicator-fin-sequence-type-Ring R n i j)
  is-central-element-indicator-fin-sequence-type-Ring j
    with has-decidable-equality-Fin n i j
  ... | inl i=j = is-central-element-one-Ring R
  ... | inr i≠j = is-central-element-zero-Ring R
```

### The dot product of an indicator sequence for index `i` with a finite sequence `v` is `v i`

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  (i : Fin n)
  where abstract

  left-dot-product-indicator-fin-sequence-type-Ring :
    (u : fin-sequence-type-Ring R n) →
    dot-product-fin-sequence-type-Ring R n
      ( indicator-fin-sequence-type-Ring R n i)
      ( u) ＝
    u i
  left-dot-product-indicator-fin-sequence-type-Ring u =
    equational-reasoning
      dot-product-fin-sequence-type-Ring R n
        ( indicator-fin-sequence-type-Ring R n i)
        ( u)
      ＝
        sum-finite-Ab
          ( ab-Ring R)
          ( Fin-Finite-Type n)
          ( λ j → mul-Ring R (indicator-fin-sequence-type-Ring R n i j) (u j))
        by
          inv
            ( eq-sum-finite-sum-count-Ab
              ( ab-Ring R)
              ( Fin-Finite-Type n)
              ( count-Fin n)
              ( _))
      ＝
        sum-finite-Ab
          ( ab-Ring R)
          ( finite-type-subset-Finite-Type
            ( Fin-Finite-Type n)
            ( decidable-standard-singleton-subtype-Discrete-Type
              ( Fin-Discrete-Type n)
              ( i)))
          ( λ (j , _) →
            mul-Ring R (indicator-fin-sequence-type-Ring R n i j) (u j))
        by
          vanish-sum-complement-decidable-subset-finite-Ab
            ( ab-Ring R)
            ( Fin-Finite-Type n)
            ( decidable-standard-singleton-subtype-Discrete-Type
              ( Fin-Discrete-Type n)
              ( i))
            ( _)
            ( λ j j≠i →
              equational-reasoning
                mul-Ring R (indicator-fin-sequence-type-Ring R n i j) (u j)
                ＝ mul-Ring R (zero-Ring R) (u j)
                  by
                    ap-mul-Ring R
                      ( compute-at-other-index-indicator-fin-sequence-type-Ring
                        ( R)
                        ( n)
                        ( i)
                        ( j)
                        ( is-symmetric-nonequal j i j≠i))
                      ( refl)
                ＝ zero-Ring R
                  by left-zero-law-mul-Ring R (u j))
      ＝ mul-Ring R (indicator-fin-sequence-type-Ring R n i i) (u i)
        by
          sum-finite-is-contr-Ab
            ( ab-Ring R)
            ( _)
            ( is-contr-type-decidable-standard-singleton-subtype-Discrete-Type
              ( Fin-Discrete-Type n)
              ( i))
            ( i , refl)
            ( _)
      ＝ mul-Ring R (one-Ring R) (u i)
        by
          ap-mul-Ring R
            ( compute-at-index-indicator-fin-sequence-type-Ring R n i)
            ( refl)
      ＝ u i
        by left-unit-law-mul-Ring R (u i)

  right-dot-product-indicator-fin-sequence-type-Ring :
    (u : fin-sequence-type-Ring R n) →
    dot-product-fin-sequence-type-Ring R n
      ( u)
      ( indicator-fin-sequence-type-Ring R n i) ＝
    u i
  right-dot-product-indicator-fin-sequence-type-Ring u =
    ( htpy-sum-fin-sequence-type-Ring R n
      ( λ j →
        inv
          ( is-central-element-indicator-fin-sequence-type-Ring
            ( R)
            ( n)
            ( i)
            ( j)
            ( u j)))) ∙
    ( left-dot-product-indicator-fin-sequence-type-Ring u)
```

### Every finite sequence in a ring is a linear combination of indicator sequences

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  (v : fin-sequence-type-Ring R n)
  where abstract

  htpy-linear-combination-indicator-fin-sequence-type-Ring :
    sum-fin-sequence-type-left-module-Ring
      ( R)
      ( left-module-fin-sequence-Ring R n)
      ( n)
      ( λ i →
        scalar-mul-fin-sequence-type-Ring R n
          ( v i)
          ( indicator-fin-sequence-type-Ring R n i)) ~
    v
  htpy-linear-combination-indicator-fin-sequence-type-Ring k =
    equational-reasoning
      sum-fin-sequence-type-left-module-Ring R
        ( left-module-fin-sequence-Ring R n) n
        ( λ i →
          scalar-mul-fin-sequence-type-Ring R n
            ( v i)
            ( indicator-fin-sequence-type-Ring R n i))
        ( k)
      ＝
        sum-fin-sequence-type-Ring
          ( R)
          ( n)
          ( λ j →
            mul-Ring
              ( R)
              ( v j)
              ( indicator-fin-sequence-type-Ring R n j k))
        by coordinate-sum-fin-sequence-fin-sequence-type-Ring R n n k _
      ＝
        sum-fin-sequence-type-Ring
          ( R)
          ( n)
          ( λ j →
            mul-Ring
              ( R)
              ( v j)
              ( indicator-fin-sequence-type-Ring R n k j))
        by
          htpy-sum-fin-sequence-type-Ring R n
            ( λ j →
              ap-mul-Ring R
                ( refl)
                ( symmetric-indicator-fin-sequence-type-Ring R n j k))
      ＝ v k
        by right-dot-product-indicator-fin-sequence-type-Ring R n k v

  eq-linear-combination-indicator-fin-sequence-type-Ring :
    sum-fin-sequence-type-left-module-Ring
      ( R)
      ( left-module-fin-sequence-Ring R n)
      ( n)
      ( λ i →
        scalar-mul-fin-sequence-type-Ring R n
          ( v i)
          ( indicator-fin-sequence-type-Ring R n i)) ＝
    v
  eq-linear-combination-indicator-fin-sequence-type-Ring =
    eq-htpy htpy-linear-combination-indicator-fin-sequence-type-Ring
```
