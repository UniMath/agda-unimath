# MacNeille real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.complements-subtypes
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-cartesian-product-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.similarity-subtypes
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universal-quantification
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

A {{#concept "MacNeille real number" Agda=macneille-ℝ}} is an
{{#concept "open Dedekind-MacNeille cut" Agda=is-open-dedekind-macneille-lower-upper-ℝ}}
`(L , U)` of [rational numbers](elementary-number-theory.rational-numbers.md),
i.e., a lower cut `L` and an upper cut `U` satisfying

- `q ∈ U` iff there exists `p < q` with `p ∉ L`
- `p ∈ L` iff there exists `q > p` with `q ∉ U`.

## Definitions

### Open Dedekind-MacNeille cuts

```agda
module _
  {l1 l2 : Level} (L : lower-ℝ l1) (U : upper-ℝ l2)
  where

  is-open-upper-complement-lower-cut-prop-lower-upper-ℝ :
    Prop (l1 ⊔ l2)
  is-open-upper-complement-lower-cut-prop-lower-upper-ℝ =
    ∀' ℚ
      ( λ q →
        cut-upper-ℝ U q ⇔
        ∃ ℚ (λ p → le-ℚ-Prop p q ∧ ¬' cut-lower-ℝ L p))

  is-open-upper-complement-lower-cut-lower-upper-ℝ :
    UU (l1 ⊔ l2)
  is-open-upper-complement-lower-cut-lower-upper-ℝ =
    type-Prop is-open-upper-complement-lower-cut-prop-lower-upper-ℝ

  is-open-lower-complement-upper-cut-prop-lower-upper-ℝ :
    Prop (l1 ⊔ l2)
  is-open-lower-complement-upper-cut-prop-lower-upper-ℝ =
    ∀' ℚ
      ( λ p →
        cut-lower-ℝ L p ⇔
        ∃ ℚ (λ q → le-ℚ-Prop p q ∧ ¬' cut-upper-ℝ U q))

  is-open-lower-complement-upper-cut-lower-upper-ℝ :
    UU (l1 ⊔ l2)
  is-open-lower-complement-upper-cut-lower-upper-ℝ =
    type-Prop is-open-lower-complement-upper-cut-prop-lower-upper-ℝ

  is-open-dedekind-macneille-prop-lower-upper-ℝ : Prop (l1 ⊔ l2)
  is-open-dedekind-macneille-prop-lower-upper-ℝ =
    is-open-upper-complement-lower-cut-prop-lower-upper-ℝ ∧
    is-open-lower-complement-upper-cut-prop-lower-upper-ℝ

  is-open-dedekind-macneille-lower-upper-ℝ : UU (l1 ⊔ l2)
  is-open-dedekind-macneille-lower-upper-ℝ =
    type-Prop is-open-dedekind-macneille-prop-lower-upper-ℝ
```

### The type of MacNeille real numbers

```agda
subtype-macneille-ℝ : (l : Level) → subtype l (lower-ℝ l × upper-ℝ l)
subtype-macneille-ℝ l x =
  is-open-dedekind-macneille-prop-lower-upper-ℝ (pr1 x) (pr2 x)

macneille-ℝ : (l : Level) → UU (lsuc l)
macneille-ℝ l = type-subtype (subtype-macneille-ℝ l)

module _
  {l : Level} (x : macneille-ℝ l)
  where

  lower-real-macneille-ℝ : lower-ℝ l
  lower-real-macneille-ℝ = pr1 (pr1 x)

  upper-real-macneille-ℝ : upper-ℝ l
  upper-real-macneille-ℝ = pr2 (pr1 x)

  lower-cut-macneille-ℝ : subtype l ℚ
  lower-cut-macneille-ℝ = cut-lower-ℝ lower-real-macneille-ℝ

  upper-cut-macneille-ℝ : subtype l ℚ
  upper-cut-macneille-ℝ = cut-upper-ℝ upper-real-macneille-ℝ

  is-in-lower-cut-macneille-ℝ : ℚ → UU l
  is-in-lower-cut-macneille-ℝ =
    is-in-cut-lower-ℝ lower-real-macneille-ℝ

  is-in-upper-cut-macneille-ℝ : ℚ → UU l
  is-in-upper-cut-macneille-ℝ =
    is-in-cut-upper-ℝ upper-real-macneille-ℝ

  is-inhabited-lower-cut-macneille-ℝ : exists ℚ lower-cut-macneille-ℝ
  is-inhabited-lower-cut-macneille-ℝ =
    is-inhabited-cut-lower-ℝ lower-real-macneille-ℝ

  is-inhabited-upper-cut-macneille-ℝ : exists ℚ upper-cut-macneille-ℝ
  is-inhabited-upper-cut-macneille-ℝ =
    is-inhabited-cut-upper-ℝ upper-real-macneille-ℝ

  is-open-dedekind-macneille-macneille-ℝ :
    is-open-dedekind-macneille-lower-upper-ℝ
      ( lower-real-macneille-ℝ)
      ( upper-real-macneille-ℝ)
  is-open-dedekind-macneille-macneille-ℝ = pr2 x

  is-open-upper-complement-lower-cut-macneille-ℝ :
    (q : ℚ) →
    is-in-upper-cut-macneille-ℝ q ↔
    exists ℚ (λ p → le-ℚ-Prop p q ∧ ¬' lower-cut-macneille-ℝ p)
  is-open-upper-complement-lower-cut-macneille-ℝ =
    pr1 is-open-dedekind-macneille-macneille-ℝ

  is-open-lower-complement-upper-cut-macneille-ℝ :
    (p : ℚ) →
    is-in-lower-cut-macneille-ℝ p ↔
    exists ℚ (λ q → le-ℚ-Prop p q ∧ ¬' upper-cut-macneille-ℝ q)
  is-open-lower-complement-upper-cut-macneille-ℝ =
    pr2 is-open-dedekind-macneille-macneille-ℝ
```

## Properties

### The MacNeille real numbers form a set

```agda
abstract
  is-set-macneille-ℝ : (l : Level) → is-set (macneille-ℝ l)
  is-set-macneille-ℝ l =
    is-set-type-subtype
      ( subtype-macneille-ℝ l)
      ( is-set-product (is-set-lower-ℝ l) (is-set-upper-ℝ l))
```

### Equality of MacNeille real numbers

```agda
eq-macneille-ℝ :
  {l : Level} (x y : macneille-ℝ l) →
  lower-real-macneille-ℝ x ＝ lower-real-macneille-ℝ y →
  upper-real-macneille-ℝ x ＝ upper-real-macneille-ℝ y →
  x ＝ y
eq-macneille-ℝ {l} _ _ p q =
  eq-type-subtype (subtype-macneille-ℝ l) (eq-pair p q)
```

### Disjointness of lower and upper cuts

```agda
abstract
  is-not-in-upper-cut-is-in-lower-cut-macneille-ℝ :
    {l : Level} (x : macneille-ℝ l) (q : ℚ) →
    is-in-lower-cut-macneille-ℝ x q →
    ¬ is-in-upper-cut-macneille-ℝ x q
  is-not-in-upper-cut-is-in-lower-cut-macneille-ℝ x q q∈L q∈U =
    let open do-syntax-trunc-Prop empty-Prop
    in do
      (r , q<r , r∉U) ←
        forward-implication
          ( is-open-lower-complement-upper-cut-macneille-ℝ x q)
          ( q∈L)
      r∉U
        ( is-in-cut-le-ℚ-upper-ℝ
          ( upper-real-macneille-ℝ x)
          ( q)
          ( r)
          ( q<r)
          ( q∈U))

  is-disjoint-cut-macneille-ℝ :
    {l : Level} (x : macneille-ℝ l) (q : ℚ) →
    ¬ (is-in-lower-cut-macneille-ℝ x q × is-in-upper-cut-macneille-ℝ x q)
  is-disjoint-cut-macneille-ℝ x q (lq , uq) =
    is-not-in-upper-cut-is-in-lower-cut-macneille-ℝ x q lq uq
```

## External links

- [MacNeille real number](https://ncatlab.org/nlab/show/MacNeille+real+number)
  on $n$Lab
