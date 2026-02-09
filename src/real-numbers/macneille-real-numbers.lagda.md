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
  is-set-macneille-ℝ : {l : Level} → is-set (macneille-ℝ l)
  is-set-macneille-ℝ {l} =
    is-set-type-subtype
      ( subtype-macneille-ℝ l)
      ( is-set-product (is-set-lower-ℝ l) (is-set-upper-ℝ l))

set-macneille-ℝ : (l : Level) → Set (lsuc l)
set-macneille-ℝ l = (macneille-ℝ l , is-set-macneille-ℝ)
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

### Characterization of each cut by the other

#### The lower cut is the subtype of rationals bounded above by some element of the complement of the upper cut

```agda
module _
  {l : Level} (x : macneille-ℝ l)
  where

  is-lower-complement-upper-cut-prop-macneille-ℝ : (p q : ℚ) → Prop l
  is-lower-complement-upper-cut-prop-macneille-ℝ p q =
    ( le-ℚ-Prop p q) ∧ (¬' (upper-cut-macneille-ℝ x q))

  lower-complement-upper-cut-macneille-ℝ : subtype l ℚ
  lower-complement-upper-cut-macneille-ℝ p =
    ∃ ℚ (is-lower-complement-upper-cut-prop-macneille-ℝ p)

  is-in-lower-complement-upper-cut-macneille-ℝ : ℚ → UU l
  is-in-lower-complement-upper-cut-macneille-ℝ =
    is-in-subtype lower-complement-upper-cut-macneille-ℝ
```

```agda
module _
  {l : Level} (x : macneille-ℝ l)
  where

  subset-lower-cut-lower-complement-upper-cut-macneille-ℝ :
    lower-complement-upper-cut-macneille-ℝ x ⊆ lower-cut-macneille-ℝ x
  subset-lower-cut-lower-complement-upper-cut-macneille-ℝ p =
    backward-implication (is-open-lower-complement-upper-cut-macneille-ℝ x p)

  subset-lower-complement-upper-cut-lower-cut-macneille-ℝ :
    lower-cut-macneille-ℝ x ⊆ lower-complement-upper-cut-macneille-ℝ x
  subset-lower-complement-upper-cut-lower-cut-macneille-ℝ p =
    forward-implication (is-open-lower-complement-upper-cut-macneille-ℝ x p)

  sim-lower-cut-lower-complement-upper-cut-macneille-ℝ :
    sim-subtype
      ( lower-complement-upper-cut-macneille-ℝ x)
      ( lower-cut-macneille-ℝ x)
  sim-lower-cut-lower-complement-upper-cut-macneille-ℝ =
    ( subset-lower-cut-lower-complement-upper-cut-macneille-ℝ ,
      subset-lower-complement-upper-cut-lower-cut-macneille-ℝ)

  eq-lower-cut-lower-complement-upper-cut-macneille-ℝ :
    lower-complement-upper-cut-macneille-ℝ x ＝ lower-cut-macneille-ℝ x
  eq-lower-cut-lower-complement-upper-cut-macneille-ℝ =
    eq-sim-subtype
      ( lower-complement-upper-cut-macneille-ℝ x)
      ( lower-cut-macneille-ℝ x)
      ( sim-lower-cut-lower-complement-upper-cut-macneille-ℝ)
```

#### The upper cut is the subtype of rationals bounded below by some element of the complement of the lower cut

```agda
module _
  {l : Level} (x : macneille-ℝ l)
  where

  is-upper-complement-lower-cut-prop-macneille-ℝ : (q p : ℚ) → Prop l
  is-upper-complement-lower-cut-prop-macneille-ℝ q p =
    (le-ℚ-Prop p q) ∧ (¬' (lower-cut-macneille-ℝ x p))

  upper-complement-lower-cut-macneille-ℝ : subtype l ℚ
  upper-complement-lower-cut-macneille-ℝ q =
    ∃ ℚ (is-upper-complement-lower-cut-prop-macneille-ℝ q)

  is-in-upper-complement-lower-cut-macneille-ℝ : ℚ → UU l
  is-in-upper-complement-lower-cut-macneille-ℝ =
    is-in-subtype upper-complement-lower-cut-macneille-ℝ
```

```agda
module _
  {l : Level} (x : macneille-ℝ l)
  where

  subset-upper-cut-upper-complement-lower-cut-macneille-ℝ :
    upper-complement-lower-cut-macneille-ℝ x ⊆ upper-cut-macneille-ℝ x
  subset-upper-cut-upper-complement-lower-cut-macneille-ℝ q =
    backward-implication
      ( is-open-upper-complement-lower-cut-macneille-ℝ x q)

  subset-upper-complement-lower-cut-upper-cut-macneille-ℝ :
    upper-cut-macneille-ℝ x ⊆ upper-complement-lower-cut-macneille-ℝ x
  subset-upper-complement-lower-cut-upper-cut-macneille-ℝ q =
    forward-implication
      ( is-open-upper-complement-lower-cut-macneille-ℝ x q)

  sim-upper-cut-upper-complement-lower-cut-macneille-ℝ :
    sim-subtype
      ( upper-complement-lower-cut-macneille-ℝ x)
      ( upper-cut-macneille-ℝ x)
  sim-upper-cut-upper-complement-lower-cut-macneille-ℝ =
    ( subset-upper-cut-upper-complement-lower-cut-macneille-ℝ ,
      subset-upper-complement-lower-cut-upper-cut-macneille-ℝ)

  eq-upper-cut-upper-complement-lower-cut-macneille-ℝ :
    upper-complement-lower-cut-macneille-ℝ x ＝ upper-cut-macneille-ℝ x
  eq-upper-cut-upper-complement-lower-cut-macneille-ℝ =
    eq-sim-subtype
      ( upper-complement-lower-cut-macneille-ℝ x)
      ( upper-cut-macneille-ℝ x)
      ( sim-upper-cut-upper-complement-lower-cut-macneille-ℝ)
```

### The lower/upper cut of a MacNeille real determines the other

```agda
module _
  {l1 l2 : Level} (x : macneille-ℝ l1) (y : macneille-ℝ l2)
  where

  subset-lower-cut-upper-cut-macneille-ℝ :
    upper-cut-macneille-ℝ y ⊆ upper-cut-macneille-ℝ x →
    lower-cut-macneille-ℝ x ⊆ lower-cut-macneille-ℝ y
  subset-lower-cut-upper-cut-macneille-ℝ H =
    binary-tr
      ( _⊆_)
      ( eq-lower-cut-lower-complement-upper-cut-macneille-ℝ x)
      ( eq-lower-cut-lower-complement-upper-cut-macneille-ℝ y)
      ( λ p → map-tot-exists (λ q → tot (λ _ K → K ∘ H q)))

  subset-upper-cut-lower-cut-macneille-ℝ :
    lower-cut-macneille-ℝ x ⊆ lower-cut-macneille-ℝ y →
    upper-cut-macneille-ℝ y ⊆ upper-cut-macneille-ℝ x
  subset-upper-cut-lower-cut-macneille-ℝ H =
    binary-tr
      ( _⊆_)
      ( eq-upper-cut-upper-complement-lower-cut-macneille-ℝ y)
      ( eq-upper-cut-upper-complement-lower-cut-macneille-ℝ x)
      ( λ q → map-tot-exists (λ p → tot (λ _ K → K ∘ H p)))

module _
  {l1 l2 : Level} (x : macneille-ℝ l1) (y : macneille-ℝ l2)
  where

  sim-lower-cut-sim-upper-cut-macneille-ℝ :
    sim-subtype (upper-cut-macneille-ℝ x) (upper-cut-macneille-ℝ y) →
    sim-subtype (lower-cut-macneille-ℝ x) (lower-cut-macneille-ℝ y)
  pr1 (sim-lower-cut-sim-upper-cut-macneille-ℝ (_ , uy⊆ux)) =
    subset-lower-cut-upper-cut-macneille-ℝ x y uy⊆ux
  pr2 (sim-lower-cut-sim-upper-cut-macneille-ℝ (ux⊆uy , _)) =
    subset-lower-cut-upper-cut-macneille-ℝ y x ux⊆uy

  sim-upper-cut-sim-lower-cut-macneille-ℝ :
    sim-subtype (lower-cut-macneille-ℝ x) (lower-cut-macneille-ℝ y) →
    sim-subtype (upper-cut-macneille-ℝ x) (upper-cut-macneille-ℝ y)
  pr1 (sim-upper-cut-sim-lower-cut-macneille-ℝ (_ , ly⊆lx)) =
    subset-upper-cut-lower-cut-macneille-ℝ y x ly⊆lx
  pr2 (sim-upper-cut-sim-lower-cut-macneille-ℝ (lx⊆ly , _)) =
    subset-upper-cut-lower-cut-macneille-ℝ x y lx⊆ly

module _
  {l : Level} (x y : macneille-ℝ l)
  where

  eq-lower-cut-eq-upper-cut-macneille-ℝ :
    upper-cut-macneille-ℝ x ＝ upper-cut-macneille-ℝ y →
    lower-cut-macneille-ℝ x ＝ lower-cut-macneille-ℝ y
  eq-lower-cut-eq-upper-cut-macneille-ℝ H =
    eq-sim-subtype
      ( lower-cut-macneille-ℝ x)
      ( lower-cut-macneille-ℝ y)
      ( sim-lower-cut-sim-upper-cut-macneille-ℝ
        ( x)
        ( y)
        ( tr
          ( sim-subtype (upper-cut-macneille-ℝ x))
          ( H)
          ( refl-sim-subtype (upper-cut-macneille-ℝ x))))

  eq-lower-real-eq-upper-real-macneille-ℝ :
    upper-real-macneille-ℝ x ＝ upper-real-macneille-ℝ y →
    lower-real-macneille-ℝ x ＝ lower-real-macneille-ℝ y
  eq-lower-real-eq-upper-real-macneille-ℝ ux=uy =
    eq-eq-cut-lower-ℝ
      ( lower-real-macneille-ℝ x)
      ( lower-real-macneille-ℝ y)
      ( eq-lower-cut-eq-upper-cut-macneille-ℝ
        ( ap cut-upper-ℝ ux=uy))

  eq-upper-cut-eq-lower-cut-macneille-ℝ :
    lower-cut-macneille-ℝ x ＝ lower-cut-macneille-ℝ y →
    upper-cut-macneille-ℝ x ＝ upper-cut-macneille-ℝ y
  eq-upper-cut-eq-lower-cut-macneille-ℝ H =
    antisymmetric-leq-subtype
      ( upper-cut-macneille-ℝ x)
      ( upper-cut-macneille-ℝ y)
      ( subset-upper-cut-lower-cut-macneille-ℝ y x
        ( pr2 ∘ has-same-elements-eq-subtype
          ( lower-cut-macneille-ℝ x)
          ( lower-cut-macneille-ℝ y)
          ( H)))
      ( subset-upper-cut-lower-cut-macneille-ℝ x y
        ( pr1 ∘ has-same-elements-eq-subtype
          ( lower-cut-macneille-ℝ x)
          ( lower-cut-macneille-ℝ y)
          ( H)))

  eq-upper-real-eq-lower-real-macneille-ℝ :
    lower-real-macneille-ℝ x ＝ lower-real-macneille-ℝ y →
    upper-real-macneille-ℝ x ＝ upper-real-macneille-ℝ y
  eq-upper-real-eq-lower-real-macneille-ℝ lx=ly =
    eq-eq-cut-upper-ℝ
      ( upper-real-macneille-ℝ x)
      ( upper-real-macneille-ℝ y)
      ( eq-upper-cut-eq-lower-cut-macneille-ℝ
        ( ap cut-lower-ℝ lx=ly))
```

### Two MacNeille real numbers with the same lower/upper real are equal

```agda
module _
  {l : Level} (x y : macneille-ℝ l)
  where

  eq-eq-lower-real-macneille-ℝ :
    lower-real-macneille-ℝ x ＝ lower-real-macneille-ℝ y → x ＝ y
  eq-eq-lower-real-macneille-ℝ lx=ly =
    eq-macneille-ℝ x y
      ( lx=ly)
      ( eq-upper-real-eq-lower-real-macneille-ℝ x y lx=ly)

  eq-eq-upper-real-macneille-ℝ :
    upper-real-macneille-ℝ x ＝ upper-real-macneille-ℝ y → x ＝ y
  eq-eq-upper-real-macneille-ℝ =
    eq-eq-lower-real-macneille-ℝ ∘
    eq-lower-real-eq-upper-real-macneille-ℝ x y

  eq-eq-lower-cut-macneille-ℝ :
    lower-cut-macneille-ℝ x ＝ lower-cut-macneille-ℝ y → x ＝ y
  eq-eq-lower-cut-macneille-ℝ =
    eq-eq-lower-real-macneille-ℝ ∘
    eq-eq-cut-lower-ℝ
      ( lower-real-macneille-ℝ x)
      ( lower-real-macneille-ℝ y)

  eq-eq-upper-cut-macneille-ℝ :
    upper-cut-macneille-ℝ x ＝ upper-cut-macneille-ℝ y → x ＝ y
  eq-eq-upper-cut-macneille-ℝ =
    eq-eq-lower-cut-macneille-ℝ ∘
    eq-lower-cut-eq-upper-cut-macneille-ℝ x y
```

## See also

- In
  [located MacNeille real numbers](real-numbers.located-macneille-real-numbers.md)
  we consider when MacNeille and Dedekind real numbers coincide.

## External links

- [MacNeille real number](https://ncatlab.org/nlab/show/MacNeille+real+number)
  on $n$Lab
