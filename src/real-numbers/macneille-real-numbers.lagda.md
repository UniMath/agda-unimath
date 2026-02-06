# MacNeille real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.complements-subtypes
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-cartesian-product-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universal-quantification
open import foundation.universe-levels

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

  is-open-upper-complement-lower-cut-prop-lower-upper-macneille-ℝ :
    Prop (l1 ⊔ l2)
  is-open-upper-complement-lower-cut-prop-lower-upper-macneille-ℝ =
    ∀' ℚ
      ( λ q → cut-upper-ℝ U q ⇔
      ∃ ℚ (λ p → le-ℚ-Prop p q ∧ ¬' cut-lower-ℝ L p))

  is-open-upper-complement-lower-cut-lower-upper-macneille-ℝ :
    UU (l1 ⊔ l2)
  is-open-upper-complement-lower-cut-lower-upper-macneille-ℝ =
    type-Prop is-open-upper-complement-lower-cut-prop-lower-upper-macneille-ℝ

  is-open-lower-complement-upper-cut-prop-lower-upper-macneille-ℝ :
    Prop (l1 ⊔ l2)
  is-open-lower-complement-upper-cut-prop-lower-upper-macneille-ℝ =
    ∀' ℚ
      ( λ p →
        cut-lower-ℝ L p ⇔
        ∃ ℚ (λ q → le-ℚ-Prop p q ∧ ¬' cut-upper-ℝ U q))

  is-open-lower-complement-upper-cut-lower-upper-macneille-ℝ :
    UU (l1 ⊔ l2)
  is-open-lower-complement-upper-cut-lower-upper-macneille-ℝ =
    type-Prop is-open-lower-complement-upper-cut-prop-lower-upper-macneille-ℝ

  is-open-dedekind-macneille-prop-lower-upper-ℝ : Prop (l1 ⊔ l2)
  is-open-dedekind-macneille-prop-lower-upper-ℝ =
    is-open-upper-complement-lower-cut-prop-lower-upper-macneille-ℝ ∧
    is-open-lower-complement-upper-cut-prop-lower-upper-macneille-ℝ

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

lower-macneille-ℝ : {l : Level} → macneille-ℝ l → lower-ℝ l
lower-macneille-ℝ = pr1 ∘ pr1

upper-macneille-ℝ : {l : Level} → macneille-ℝ l → upper-ℝ l
upper-macneille-ℝ = pr2 ∘ pr1

lower-cut-macneille-ℝ : {l : Level} → macneille-ℝ l → subtype l ℚ
lower-cut-macneille-ℝ x = cut-lower-ℝ (lower-macneille-ℝ x)

upper-cut-macneille-ℝ : {l : Level} → macneille-ℝ l → subtype l ℚ
upper-cut-macneille-ℝ x = cut-upper-ℝ (upper-macneille-ℝ x)

is-in-lower-cut-macneille-ℝ : {l : Level} → macneille-ℝ l → ℚ → UU l
is-in-lower-cut-macneille-ℝ x =
  is-in-cut-lower-ℝ (lower-macneille-ℝ x)

is-in-upper-cut-macneille-ℝ : {l : Level} → macneille-ℝ l → ℚ → UU l
is-in-upper-cut-macneille-ℝ x =
  is-in-cut-upper-ℝ (upper-macneille-ℝ x)

is-open-dedekind-macneille-macneille-ℝ :
  {l : Level} (x : macneille-ℝ l) →
  is-open-dedekind-macneille-lower-upper-ℝ
    ( lower-macneille-ℝ x)
    ( upper-macneille-ℝ x)
is-open-dedekind-macneille-macneille-ℝ = pr2

is-open-upper-complement-lower-cut-macneille-ℝ :
  {l : Level} (x : macneille-ℝ l) (q : ℚ) →
  is-in-upper-cut-macneille-ℝ x q ↔
  exists ℚ (λ p → le-ℚ-Prop p q ∧ ¬' (lower-cut-macneille-ℝ x p))
is-open-upper-complement-lower-cut-macneille-ℝ x =
  pr1 (is-open-dedekind-macneille-macneille-ℝ x)

is-open-lower-complement-upper-cut-macneille-ℝ :
  {l : Level} (x : macneille-ℝ l) (p : ℚ) →
  is-in-lower-cut-macneille-ℝ x p ↔
  exists ℚ (λ q → le-ℚ-Prop p q ∧ ¬' (upper-cut-macneille-ℝ x q))
is-open-lower-complement-upper-cut-macneille-ℝ x =
  pr2 (is-open-dedekind-macneille-macneille-ℝ x)

cut-macneille-ℝ : {l : Level} → macneille-ℝ l → subtype l ℚ
cut-macneille-ℝ = cut-lower-ℝ ∘ lower-macneille-ℝ

cut-upper-macneille-ℝ : {l : Level} → macneille-ℝ l → subtype l ℚ
cut-upper-macneille-ℝ = cut-upper-ℝ ∘ upper-macneille-ℝ
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
  lower-macneille-ℝ x ＝ lower-macneille-ℝ y →
  upper-macneille-ℝ x ＝ upper-macneille-ℝ y →
  x ＝ y
eq-macneille-ℝ {l} _ _ p q =
  eq-type-subtype (subtype-macneille-ℝ l) (eq-pair p q)
```

### Disjointedness of lower and upper cuts

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
          ( upper-macneille-ℝ x)
          ( q)
          ( r)
          ( q<r)
          ( q∈U))
```

## External links

- [MacNeille real number](https://ncatlab.org/nlab/show/MacNeille+real+number)
  on $n$Lab
