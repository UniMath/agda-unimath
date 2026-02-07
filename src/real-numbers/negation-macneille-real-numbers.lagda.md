# Negation of MacNeille real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.negation-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjoint-subtypes
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.raising-universe-levels
open import foundation.similarity-subtypes
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.negation-lower-upper-dedekind-real-numbers
open import real-numbers.raising-universe-levels-macneille-real-numbers
open import real-numbers.rational-macneille-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-macneille-real-numbers
open import real-numbers.strict-inequality-macneille-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The
{{#concept "negation" Disambiguation="MacNeille real number" Agda=neg-macneille-ℝ}}
of a [MacNeille real number](real-numbers.macneille-real-numbers.md) with cuts
`(L, U)` has lower cut equal to the negation of elements of `U`, and upper cut
equal to the negation of elements in `L`.

```agda
module _
  {l : Level} (x : macneille-ℝ l)
  where

  lower-real-neg-macneille-ℝ : lower-ℝ l
  lower-real-neg-macneille-ℝ = neg-upper-ℝ (upper-real-macneille-ℝ x)

  upper-real-neg-macneille-ℝ : upper-ℝ l
  upper-real-neg-macneille-ℝ = neg-lower-ℝ (lower-real-macneille-ℝ x)

  lower-cut-neg-macneille-ℝ : subtype l ℚ
  lower-cut-neg-macneille-ℝ = cut-lower-ℝ lower-real-neg-macneille-ℝ

  upper-cut-neg-macneille-ℝ : subtype l ℚ
  upper-cut-neg-macneille-ℝ = cut-upper-ℝ upper-real-neg-macneille-ℝ

  is-in-lower-cut-neg-macneille-ℝ : ℚ → UU l
  is-in-lower-cut-neg-macneille-ℝ = is-in-subtype lower-cut-neg-macneille-ℝ

  is-in-upper-cut-neg-macneille-ℝ : ℚ → UU l
  is-in-upper-cut-neg-macneille-ℝ = is-in-subtype upper-cut-neg-macneille-ℝ

  is-disjoint-cut-neg-macneille-ℝ :
    disjoint-subtype lower-cut-neg-macneille-ℝ upper-cut-neg-macneille-ℝ
  is-disjoint-cut-neg-macneille-ℝ q (in-lower-neg , in-upper-neg) =
    is-disjoint-cut-macneille-ℝ x (neg-ℚ q) (in-upper-neg , in-lower-neg)

  forward-implication-is-open-upper-complement-lower-cut-neg-macneille-ℝ :
    (q : ℚ) →
    is-in-upper-cut-neg-macneille-ℝ q →
    exists ℚ (λ p → le-ℚ-Prop p q ∧ ¬' lower-cut-neg-macneille-ℝ p)
  forward-implication-is-open-upper-complement-lower-cut-neg-macneille-ℝ
    q q∈Uneg =
    map-exists
      ( λ p → (le-ℚ p q) × (¬ (is-in-lower-cut-neg-macneille-ℝ p)))
      ( neg-ℚ)
      ( λ r (negq≤r , r∉U) →
        tr (le-ℚ (neg-ℚ r)) (neg-neg-ℚ q) (neg-le-ℚ negq≤r) ,
        ( λ u → r∉U (tr (is-in-upper-cut-macneille-ℝ x) (neg-neg-ℚ r) u)))
      ( forward-implication
        ( is-open-lower-complement-upper-cut-macneille-ℝ x (neg-ℚ q))
        ( q∈Uneg))

  backward-implication-is-open-upper-complement-lower-cut-neg-macneille-ℝ :
    (q : ℚ) →
    exists ℚ (λ p → le-ℚ-Prop p q ∧ ¬' lower-cut-neg-macneille-ℝ p) →
    is-in-upper-cut-neg-macneille-ℝ q
  backward-implication-is-open-upper-complement-lower-cut-neg-macneille-ℝ q =
    elim-exists
      ( upper-cut-neg-macneille-ℝ q)
      ( λ p (p≤q , p∉Lneg) →
        backward-implication
          ( is-open-lower-complement-upper-cut-macneille-ℝ x (neg-ℚ q))
          ( intro-exists (neg-ℚ p) (neg-le-ℚ p≤q , p∉Lneg)))

  is-open-upper-complement-lower-cut-neg-macneille-ℝ :
    (q : ℚ) →
    is-in-upper-cut-neg-macneille-ℝ q ↔
    exists ℚ (λ p → le-ℚ-Prop p q ∧ ¬' lower-cut-neg-macneille-ℝ p)
  is-open-upper-complement-lower-cut-neg-macneille-ℝ q =
    ( forward-implication-is-open-upper-complement-lower-cut-neg-macneille-ℝ q ,
      backward-implication-is-open-upper-complement-lower-cut-neg-macneille-ℝ q)

  forward-implication-is-open-lower-complement-upper-cut-neg-macneille-ℝ :
    (p : ℚ) →
    is-in-lower-cut-neg-macneille-ℝ p →
    exists ℚ (λ q → le-ℚ-Prop p q ∧ ¬' upper-cut-neg-macneille-ℝ q)
  forward-implication-is-open-lower-complement-upper-cut-neg-macneille-ℝ
    p p∈Lneg =
    map-exists
      ( λ q → (le-ℚ p q) × (¬ (is-in-upper-cut-neg-macneille-ℝ q)))
      ( neg-ℚ)
      ( λ r (r≤-p , r∉L) →
        tr (λ t → le-ℚ t (neg-ℚ r)) (neg-neg-ℚ p) (neg-le-ℚ r≤-p) ,
        ( λ u →
          r∉L
            ( tr (is-in-lower-cut-macneille-ℝ x) (neg-neg-ℚ r) u)))
      ( forward-implication
        ( is-open-upper-complement-lower-cut-macneille-ℝ x (neg-ℚ p))
        p∈Lneg)

  backward-implication-is-open-lower-complement-upper-cut-neg-macneille-ℝ :
    (p : ℚ) →
    exists ℚ (λ q → le-ℚ-Prop p q ∧ ¬' upper-cut-neg-macneille-ℝ q) →
    is-in-lower-cut-neg-macneille-ℝ p
  backward-implication-is-open-lower-complement-upper-cut-neg-macneille-ℝ p =
    elim-exists
      ( lower-cut-neg-macneille-ℝ p)
      ( λ q (p≤q , q∉Uneg) →
        backward-implication
          ( is-open-upper-complement-lower-cut-macneille-ℝ x (neg-ℚ p))
          ( intro-exists (neg-ℚ q) (neg-le-ℚ p≤q , q∉Uneg)))

  is-open-lower-complement-upper-cut-neg-macneille-ℝ :
    (p : ℚ) →
    is-in-lower-cut-neg-macneille-ℝ p ↔
    exists ℚ (λ q → le-ℚ-Prop p q ∧ ¬' upper-cut-neg-macneille-ℝ q)
  is-open-lower-complement-upper-cut-neg-macneille-ℝ p =
    ( forward-implication-is-open-lower-complement-upper-cut-neg-macneille-ℝ p ,
      backward-implication-is-open-lower-complement-upper-cut-neg-macneille-ℝ p)

  is-open-dedekind-macneille-neg-macneille-ℝ :
    is-open-dedekind-macneille-lower-upper-ℝ
      ( lower-real-neg-macneille-ℝ)
      ( upper-real-neg-macneille-ℝ)
  is-open-dedekind-macneille-neg-macneille-ℝ =
    ( is-open-upper-complement-lower-cut-neg-macneille-ℝ ,
      is-open-lower-complement-upper-cut-neg-macneille-ℝ)

  opaque
    neg-macneille-ℝ : macneille-ℝ l
    neg-macneille-ℝ =
      ( ( lower-real-neg-macneille-ℝ , upper-real-neg-macneille-ℝ) ,
        is-open-dedekind-macneille-neg-macneille-ℝ)
```

## Properties

### The negation function on MacNeille real numbers is an involution

```agda
abstract opaque
  unfolding neg-macneille-ℝ

  neg-neg-macneille-ℝ :
    {l : Level} (x : macneille-ℝ l) → neg-macneille-ℝ (neg-macneille-ℝ x) ＝ x
  neg-neg-macneille-ℝ x =
    eq-eq-lower-cut-macneille-ℝ
      ( neg-macneille-ℝ (neg-macneille-ℝ x))
      ( x)
      ( eq-has-same-elements-subtype
        ( lower-cut-macneille-ℝ (neg-macneille-ℝ (neg-macneille-ℝ x)))
        ( lower-cut-macneille-ℝ x)
        ( λ q →
          tr (is-in-lower-cut-macneille-ℝ x) (neg-neg-ℚ q) ,
          tr (is-in-lower-cut-macneille-ℝ x) (inv (neg-neg-ℚ q))))
```

### Negation preserves rationality

```agda
opaque
  unfolding neg-macneille-ℝ macneille-real-ℚ real-ℚ

  neg-macneille-real-ℚ :
    (q : ℚ) →
    neg-macneille-ℝ (macneille-real-ℚ q) ＝ macneille-real-ℚ (neg-ℚ q)
  neg-macneille-real-ℚ q =
    eq-eq-lower-real-macneille-ℝ
      ( neg-macneille-ℝ (macneille-real-ℚ q))
      ( macneille-real-ℚ (neg-ℚ q))
      ( neg-upper-real-ℚ q)

abstract
  neg-zero-macneille-ℝ :
    neg-macneille-ℝ zero-macneille-ℝ ＝ zero-macneille-ℝ
  neg-zero-macneille-ℝ =
    neg-macneille-real-ℚ zero-ℚ ∙ ap macneille-real-ℚ neg-zero-ℚ

  eq-neg-one-macneille-ℝ :
    neg-macneille-ℝ one-macneille-ℝ ＝ neg-one-macneille-ℝ
  eq-neg-one-macneille-ℝ =
    neg-macneille-real-ℚ one-ℚ ∙ ap macneille-real-ℚ eq-neg-one-ℚ
```

### The negation of the inclusion of integers in the real numbers

```agda
abstract
  neg-macneille-real-ℤ :
    (k : ℤ) →
    neg-macneille-ℝ (macneille-real-ℤ k) ＝ macneille-real-ℤ (neg-ℤ k)
  neg-macneille-real-ℤ k =
    neg-macneille-real-ℚ (rational-ℤ k) ∙
    ap macneille-real-ℚ (inv (neg-rational-ℤ k))
```

### Negation preserves similarity

```agda
abstract opaque
  unfolding neg-macneille-ℝ

  preserves-sim-neg-macneille-ℝ :
    {l1 l2 : Level} {x : macneille-ℝ l1} {x' : macneille-ℝ l2} →
    sim-macneille-ℝ x x' →
    sim-macneille-ℝ (neg-macneille-ℝ x) (neg-macneille-ℝ x')
  preserves-sim-neg-macneille-ℝ {x = x} {x' = x'} x~x' =
    let
      (lx⊆lx' , lx'⊆lx) =
        backward-implication
          ( sim-lower-cut-iff-sim-macneille-ℝ x x')
          ( x~x')
    in
      forward-implication
        ( sim-upper-cut-iff-sim-macneille-ℝ _ _)
        ( lx⊆lx' ∘ neg-ℚ , lx'⊆lx ∘ neg-ℚ)

  neg-raise-macneille-ℝ :
    {l0 : Level} (l : Level) (x : macneille-ℝ l0) →
    neg-macneille-ℝ (raise-macneille-ℝ l x) ＝
    raise-macneille-ℝ l (neg-macneille-ℝ x)
  neg-raise-macneille-ℝ l x =
    eq-sim-macneille-ℝ
      ( transitive-sim-macneille-ℝ _ _ _
        ( sim-raise-macneille-ℝ l (neg-macneille-ℝ x))
        ( preserves-sim-neg-macneille-ℝ (sim-raise-macneille-ℝ' l x)))
```

### `x = -x` if and only if `x = 0`

```agda
module _
  {l : Level} {x : macneille-ℝ l}
  (-x=x : neg-macneille-ℝ x ＝ x)
  where

  abstract opaque
    unfolding neg-macneille-ℝ real-ℚ macneille-real-ℚ

    is-in-lower-cut-zero-is-in-upper-cut-zero-eq-neg-macneille-ℝ :
      is-in-lower-cut-macneille-ℝ x zero-ℚ →
      is-in-upper-cut-macneille-ℝ x zero-ℚ
    is-in-lower-cut-zero-is-in-upper-cut-zero-eq-neg-macneille-ℝ 0∈L =
      tr
        ( is-in-upper-cut-macneille-ℝ x)
        ( neg-zero-ℚ)
        ( inv-tr
          ( λ y → is-in-lower-cut-macneille-ℝ y zero-ℚ)
          ( -x=x)
          ( 0∈L))

    is-in-upper-cut-zero-is-in-lower-cut-zero-eq-neg-macneille-ℝ :
      is-in-upper-cut-macneille-ℝ x zero-ℚ →
      is-in-lower-cut-macneille-ℝ x zero-ℚ
    is-in-upper-cut-zero-is-in-lower-cut-zero-eq-neg-macneille-ℝ 0∈U =
      tr
        ( is-in-lower-cut-macneille-ℝ x)
        ( neg-zero-ℚ)
        ( inv-tr
          ( λ y → is-in-upper-cut-macneille-ℝ y zero-ℚ)
          ( -x=x)
          ( 0∈U))

    is-not-in-upper-cut-zero-eq-neg-macneille-ℝ :
      ¬ is-in-upper-cut-macneille-ℝ x zero-ℚ
    is-not-in-upper-cut-zero-eq-neg-macneille-ℝ 0∈U =
      is-disjoint-cut-macneille-ℝ x zero-ℚ
        ( is-in-upper-cut-zero-is-in-lower-cut-zero-eq-neg-macneille-ℝ 0∈U ,
          0∈U)

    is-in-upper-cut-neg-is-in-lower-cut-eq-neg-macneille-ℝ :
      (q : ℚ) →
      is-in-lower-cut-macneille-ℝ x q →
      is-in-upper-cut-macneille-ℝ x (neg-ℚ q)
    is-in-upper-cut-neg-is-in-lower-cut-eq-neg-macneille-ℝ q =
      inv-tr (λ y → is-in-lower-cut-macneille-ℝ y q) (-x=x)

    is-in-lower-cut-raise-zero-is-in-lower-cut-eq-neg-macneille-ℝ :
      (q : ℚ) →
      is-in-lower-cut-macneille-ℝ x q →
      is-in-lower-cut-macneille-ℝ (raise-macneille-real-ℚ l zero-ℚ) q
    is-in-lower-cut-raise-zero-is-in-lower-cut-eq-neg-macneille-ℝ q q∈L =
      trichotomy-le-ℚ q zero-ℚ
        ( λ q<0 → map-raise q<0)
        ( λ q=0 →
          ex-falso
            ( is-disjoint-cut-macneille-ℝ x zero-ℚ
              ( tr (is-in-lower-cut-macneille-ℝ x) q=0 q∈L ,
                is-in-lower-cut-zero-is-in-upper-cut-zero-eq-neg-macneille-ℝ
                  ( tr (is-in-lower-cut-macneille-ℝ x) q=0 q∈L))))
        ( λ 0<q →
          ex-falso
            ( is-disjoint-cut-macneille-ℝ x zero-ℚ
              ( le-lower-cut-macneille-ℝ x 0<q q∈L ,
                le-upper-cut-macneille-ℝ x
                  ( tr
                    ( le-ℚ (neg-ℚ q))
                    ( neg-zero-ℚ)
                    ( neg-le-ℚ 0<q))
                  ( is-in-upper-cut-neg-is-in-lower-cut-eq-neg-macneille-ℝ q
                    ( q∈L)))))

    is-in-lower-cut-is-in-lower-cut-raise-zero-eq-neg-macneille-ℝ :
      (q : ℚ) →
      is-in-lower-cut-macneille-ℝ (raise-macneille-real-ℚ l zero-ℚ) q →
      is-in-lower-cut-macneille-ℝ x q
    is-in-lower-cut-is-in-lower-cut-raise-zero-eq-neg-macneille-ℝ q q<0 =
      backward-implication
        ( is-open-lower-complement-upper-cut-macneille-ℝ x q)
        ( intro-exists
          ( zero-ℚ)
          ( map-inv-raise q<0 , is-not-in-upper-cut-zero-eq-neg-macneille-ℝ))

    is-rational-zero-eq-neg-macneille-ℝ :
      is-rational-macneille-ℝ x zero-ℚ
    is-rational-zero-eq-neg-macneille-ℝ =
      eq-eq-lower-cut-macneille-ℝ
        ( x)
        ( raise-macneille-real-ℚ l zero-ℚ)
        ( eq-has-same-elements-subtype
          ( lower-cut-macneille-ℝ x)
          ( lower-cut-macneille-ℝ (raise-macneille-real-ℚ l zero-ℚ))
          ( λ q →
            ( is-in-lower-cut-raise-zero-is-in-lower-cut-eq-neg-macneille-ℝ q ,
              is-in-lower-cut-is-in-lower-cut-raise-zero-eq-neg-macneille-ℝ q)))

abstract opaque
  unfolding neg-macneille-ℝ real-ℚ macneille-real-ℚ

  eq-raise-zero-macneille-ℝ :
    {l : Level} →
    raise-zero-macneille-ℝ l ＝ raise-macneille-ℝ l zero-macneille-ℝ
  eq-raise-zero-macneille-ℝ {l} =
    eq-eq-lower-real-macneille-ℝ
      ( raise-zero-macneille-ℝ l)
      ( raise-macneille-ℝ l zero-macneille-ℝ)
      ( refl)

  sim-raise-zero-macneille-ℝ :
    {l : Level} →
    raise-zero-macneille-ℝ l ~ℝₘ zero-macneille-ℝ
  sim-raise-zero-macneille-ℝ {l} =
    transitive-sim-macneille-ℝ
      ( raise-zero-macneille-ℝ l)
      ( raise-macneille-ℝ l zero-macneille-ℝ)
      ( zero-macneille-ℝ)
      ( sim-raise-macneille-ℝ' l zero-macneille-ℝ)
      ( sim-eq-macneille-ℝ eq-raise-zero-macneille-ℝ)

  is-zero-eq-neg-macneille-ℝ :
    {l : Level} {x : macneille-ℝ l} →
    neg-macneille-ℝ x ＝ x →
    is-zero-macneille-ℝ x
  is-zero-eq-neg-macneille-ℝ {l} {x} -x=x =
    transitive-sim-macneille-ℝ x
      ( raise-zero-macneille-ℝ l)
      ( zero-macneille-ℝ)
      ( sim-raise-zero-macneille-ℝ)
      ( sim-eq-macneille-ℝ
        ( eq-raise-rational-is-rational-macneille-ℝ
          ( is-rational-zero-eq-neg-macneille-ℝ -x=x)))

  sim-neg-is-zero-macneille-ℝ :
    {l : Level} {x : macneille-ℝ l} →
    is-zero-macneille-ℝ x →
    neg-macneille-ℝ x ~ℝₘ x
  sim-neg-is-zero-macneille-ℝ {_} {x} x~0 =
    similarity-reasoning-macneille-ℝ
      neg-macneille-ℝ x
      ~ℝₘ neg-macneille-ℝ zero-macneille-ℝ
        by preserves-sim-neg-macneille-ℝ x~0
      ~ℝₘ zero-macneille-ℝ
        by sim-eq-macneille-ℝ neg-zero-macneille-ℝ
      ~ℝₘ x
        by symmetric-sim-macneille-ℝ x~0

  eq-neg-is-zero-macneille-ℝ :
    {l : Level} {x : macneille-ℝ l} →
    is-zero-macneille-ℝ x →
    neg-macneille-ℝ x ＝ x
  eq-neg-is-zero-macneille-ℝ x~0 =
    eq-sim-macneille-ℝ (sim-neg-is-zero-macneille-ℝ x~0)
```

## See also

- In
  [The negation isometry on real numbers](real-numbers.isometry-negation-real-numbers.md)
  we show that negation is an
  [isometry](metric-spaces.isometries-metric-spaces.md) on the
  [metric space of real numbers](real-numbers.metric-space-of-real-numbers.md)
