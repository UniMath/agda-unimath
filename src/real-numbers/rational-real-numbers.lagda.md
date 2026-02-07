# Rational real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.rational-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-lower-dedekind-real-numbers
open import real-numbers.rational-upper-dedekind-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

The type of [rationals](elementary-number-theory.rational-numbers.md) `ℚ`
[embeds](foundation-core.embeddings.md) into the type of
[Dedekind reals](real-numbers.dedekind-real-numbers.md) `ℝ`. We call numbers in
the [image](foundation.images.md) of this embedding
{{#concept "rational real numbers" Agda=Rational-ℝ}}.

## Definitions

### Strict inequality on rationals gives Dedekind cuts

```agda
is-dedekind-lower-upper-real-ℚ :
  (x : ℚ) →
  is-dedekind-lower-upper-ℝ (lower-real-ℚ x) (upper-real-ℚ x)
is-dedekind-lower-upper-real-ℚ x =
  ( (λ q (H , K) → asymmetric-le-ℚ q x H K) ,
    located-le-ℚ x)
```

### The inclusion of `ℚ` into `ℝ lzero`

```agda
opaque
  real-ℚ : ℚ → ℝ lzero
  real-ℚ x =
    (lower-real-ℚ x , upper-real-ℚ x , is-dedekind-lower-upper-real-ℚ x)

real-ℚ⁺ : ℚ⁺ → ℝ lzero
real-ℚ⁺ q = real-ℚ (rational-ℚ⁺ q)

real-ℚ⁰⁺ : ℚ⁰⁺ → ℝ lzero
real-ℚ⁰⁺ q = real-ℚ (rational-ℚ⁰⁺ q)
```

### The inclusion of `ℤ` into `ℝ lzero`

```agda
real-ℤ : ℤ → ℝ lzero
real-ℤ x = real-ℚ (rational-ℤ x)
```

### The inclusion of `ℕ` into `ℝ lzero`

```agda
real-ℕ : ℕ → ℝ lzero
real-ℕ n = real-ℤ (int-ℕ n)
```

### Zero as a real number

```agda
zero-ℝ : ℝ lzero
zero-ℝ = real-ℚ zero-ℚ
```

### One as a real number

```agda
one-ℝ : ℝ lzero
one-ℝ = real-ℚ one-ℚ
```

### Negative one as a real number

```agda
neg-one-ℝ : ℝ lzero
neg-one-ℝ = real-ℚ neg-one-ℚ
```

### ½ as a real number

```agda
one-half-ℝ : ℝ lzero
one-half-ℝ = real-ℚ one-half-ℚ
```

### The inclusion of `ℚ` into `ℝ l`

```agda
raise-real-ℚ : (l : Level) → ℚ → ℝ l
raise-real-ℚ l q = raise-ℝ l (real-ℚ q)

raise-zero-ℝ : (l : Level) → ℝ l
raise-zero-ℝ l = raise-real-ℚ l zero-ℚ

raise-one-ℝ : (l : Level) → ℝ l
raise-one-ℝ l = raise-real-ℚ l one-ℚ
```

### The property of being a rational real number

```agda
module _
  {l : Level} (x : ℝ l) (p : ℚ)
  where

  is-rational-prop-ℝ : Prop l
  is-rational-prop-ℝ =
    (¬' (lower-cut-ℝ x p)) ∧ (¬' (upper-cut-ℝ x p))

  is-rational-ℝ : UU l
  is-rational-ℝ = type-Prop is-rational-prop-ℝ
```

```agda
abstract
  all-eq-is-rational-ℝ :
    {l : Level} (x : ℝ l) (p q : ℚ) →
    is-rational-ℝ x p →
    is-rational-ℝ x q →
    p ＝ q
  all-eq-is-rational-ℝ x p q H H' =
    trichotomy-le-ℚ p q left-case id right-case
    where
    left-case : le-ℚ p q → p ＝ q
    left-case I =
      ex-falso
        ( elim-disjunction
          ( empty-Prop)
          ( pr1 H)
          ( pr2 H')
          ( is-located-lower-upper-cut-ℝ x I))

    right-case : le-ℚ q p → p ＝ q
    right-case I =
      ex-falso
        ( elim-disjunction
          ( empty-Prop)
          ( pr1 H')
          ( pr2 H)
          ( is-located-lower-upper-cut-ℝ x I))

abstract
  is-prop-is-rational-ℝ :
    {l : Level} (x : ℝ l) → is-prop (Σ ℚ (is-rational-ℝ x))
  is-prop-is-rational-ℝ x =
    is-prop-all-elements-equal
      ( λ p q →
        eq-type-subtype
          ( is-rational-prop-ℝ x)
          ( all-eq-is-rational-ℝ x (pr1 p) (pr1 q) (pr2 p) (pr2 q)))
```

### The subtype of rational reals

```agda
subtype-rational-ℝ : {l : Level} → ℝ l → Prop l
subtype-rational-ℝ x = (Σ ℚ (is-rational-ℝ x) , is-prop-is-rational-ℝ x)

Rational-ℝ : (l : Level) → UU (lsuc l)
Rational-ℝ l = type-subtype subtype-rational-ℝ

module _
  {l : Level} (x : Rational-ℝ l)
  where

  real-rational-ℝ : ℝ l
  real-rational-ℝ = pr1 x

  rational-rational-ℝ : ℚ
  rational-rational-ℝ = pr1 (pr2 x)

  is-rational-rational-ℝ : is-rational-ℝ real-rational-ℝ rational-rational-ℝ
  is-rational-rational-ℝ = pr2 (pr2 x)
```

## Properties

### The real embedding of a rational number is rational

```agda
abstract opaque
  unfolding real-ℚ

  is-rational-real-ℚ : (p : ℚ) → is-rational-ℝ (real-ℚ p) p
  is-rational-real-ℚ p = (irreflexive-le-ℚ p , irreflexive-le-ℚ p)
```

### A rational real number raised to another universe level is rational

```agda
abstract
  is-rational-raise-ℝ :
    {l0 : Level} (l : Level) (x : ℝ l0) {q : ℚ} →
    is-rational-ℝ x q → is-rational-ℝ (raise-ℝ l x) q
  is-rational-raise-ℝ l x (q≮x , x≮q) =
    ( q≮x ∘ map-inv-raise , x≮q ∘ map-inv-raise)

  is-rational-raise-real-ℚ :
    (l : Level) (p : ℚ) → is-rational-ℝ (raise-real-ℚ l p) p
  is-rational-raise-real-ℚ l p =
    is-rational-raise-ℝ l (real-ℚ p) (is-rational-real-ℚ p)
```

### Rational real numbers are embedded rationals

```agda
module _
  {l : Level}
  {x : ℝ l}
  {q : ℚ}
  where

  abstract opaque
    unfolding real-ℚ sim-ℝ

    is-rational-sim-rational-ℝ : sim-ℝ x (real-ℚ q) → is-rational-ℝ x q
    pr1 (is-rational-sim-rational-ℝ x~q) q<x =
      irreflexive-le-ℚ q (pr1 x~q q q<x)
    pr2 (is-rational-sim-rational-ℝ x~q) x<q =
      irreflexive-le-ℚ q (pr1 (sim-upper-cut-sim-ℝ x (real-ℚ q) x~q) q x<q)

    sim-rational-is-rational-ℝ : is-rational-ℝ x q → sim-ℝ x (real-ℚ q)
    pr1 (sim-rational-is-rational-ℝ (q≮x , x≮q)) r r<x =
      trichotomy-le-ℚ
        ( q)
        ( r)
        ( λ q<r → ex-falso (q≮x (le-lower-cut-ℝ x q<r r<x)))
        ( λ q=r → ex-falso (q≮x (inv-tr (is-in-lower-cut-ℝ x) q=r r<x)))
        ( id)
    pr2 (sim-rational-is-rational-ℝ (q≮x , x≮q)) r r<q =
      elim-disjunction
        ( lower-cut-ℝ x r)
        ( id)
        ( ex-falso ∘ x≮q)
        ( is-located-lower-upper-cut-ℝ x r<q)

  is-rational-iff-sim-rational-ℝ :
    (is-rational-ℝ x q) ↔ (sim-ℝ x (real-ℚ q))
  is-rational-iff-sim-rational-ℝ =
    ( sim-rational-is-rational-ℝ ,
      is-rational-sim-rational-ℝ)

abstract
  sim-rational-ℝ :
    {l : Level} →
    (x : Rational-ℝ l) →
    sim-ℝ (real-rational-ℝ x) (real-ℚ (rational-rational-ℝ x))
  sim-rational-ℝ (x , q , x~q) = sim-rational-is-rational-ℝ x~q

  eq-real-rational-is-rational-ℝ :
    (x : ℝ lzero) (q : ℚ) → is-rational-ℝ x q → real-ℚ q ＝ x
  eq-real-rational-is-rational-ℝ x q H =
    inv (eq-sim-ℝ {lzero} {x} {real-ℚ q} (sim-rational-ℝ (x , q , H)))

  eq-raise-real-rational-is-rational-ℝ :
    {l : Level} {x : ℝ l} {q : ℚ} → is-rational-ℝ x q → x ＝ raise-real-ℚ l q
  eq-raise-real-rational-is-rational-ℝ {l} {x} {q} x~q =
    eq-sim-ℝ
      ( transitive-sim-ℝ
        ( x)
        ( real-ℚ q)
        ( raise-real-ℚ l q)
        ( sim-raise-ℝ l (real-ℚ q))
        ( sim-rational-ℝ (x , q , x~q)))

  is-rational-eq-raise-real-rational-ℝ :
    {l : Level} {x : ℝ l} {q : ℚ} → x ＝ raise-real-ℚ l q → is-rational-ℝ x q
  is-rational-eq-raise-real-rational-ℝ {l} {x} {q} x=q =
    is-rational-sim-rational-ℝ
      ( inv-tr (λ y → sim-ℝ y (real-ℚ q)) x=q (sim-raise-ℝ' l (real-ℚ q)))

is-rational-iff-eq-raise-real-ℝ :
  {l : Level} {x : ℝ l} {q : ℚ} →
  (is-rational-ℝ x q) ↔ (x ＝ raise-real-ℚ l q)
is-rational-iff-eq-raise-real-ℝ =
  ( eq-raise-real-rational-is-rational-ℝ ,
    is-rational-eq-raise-real-rational-ℝ)
```

### The inclusion of rationals into rational reals

```agda
rational-real-ℚ : ℚ → Rational-ℝ lzero
rational-real-ℚ q = (real-ℚ q , q , is-rational-real-ℚ q)

raise-rational-real-ℚ : (l : Level) → ℚ → Rational-ℝ l
raise-rational-real-ℚ l q =
  ( raise-real-ℚ l q , q , is-rational-raise-real-ℚ l q)
```

### The rationals and rational reals are equivalent

```agda
abstract
  is-section-rational-real-ℚ :
    is-section rational-rational-ℝ rational-real-ℚ
  is-section-rational-real-ℚ q = refl

  is-retraction-rational-real-ℚ :
      is-retraction rational-rational-ℝ rational-real-ℚ
  is-retraction-rational-real-ℚ (x , q , H) =
    eq-type-subtype subtype-rational-ℝ (eq-real-rational-is-rational-ℝ x q H)

  is-equiv-rational-rational-ℝ : is-equiv (rational-rational-ℝ {lzero})
  is-equiv-rational-rational-ℝ =
    is-equiv-is-invertible
      ( rational-real-ℚ)
      ( is-section-rational-real-ℚ)
      ( is-retraction-rational-real-ℚ)

equiv-rational-ℝ : Rational-ℝ lzero ≃ ℚ
equiv-rational-ℝ = (rational-rational-ℝ , is-equiv-rational-rational-ℝ)
```

### The canonical embedding of the rational numbers in the real numbers is injective

```agda
abstract opaque
  unfolding real-ℚ

  is-injective-real-ℚ : is-injective real-ℚ
  is-injective-real-ℚ {p} {q} pℝ=qℝ =
    trichotomy-le-ℚ
      ( p)
      ( q)
      ( λ p<q →
        ex-falso
          ( irreflexive-le-ℚ
            ( p)
            ( inv-tr (λ x → is-in-lower-cut-ℝ x p) pℝ=qℝ p<q)))
      ( id)
      ( λ q<p →
        ex-falso
          ( irreflexive-le-ℚ
            ( q)
            ( tr (λ x → is-in-lower-cut-ℝ x q) pℝ=qℝ q<p)))
```

### Raising rational reals is an embedding

```agda
abstract
  is-injective-raise-real-ℚ :
    {l : Level} → is-injective (raise-real-ℚ l)
  is-injective-raise-real-ℚ {l} =
    is-injective-comp is-injective-real-ℚ (is-injective-raise-ℝ l)

  is-emb-raise-real-ℚ : {l : Level} → is-emb (raise-real-ℚ l)
  is-emb-raise-real-ℚ {l} =
    is-emb-is-injective (is-set-ℝ l) (is-injective-raise-real-ℚ {l})
```

### The inclusions are embeddings

```agda
abstract
  is-emb-real-ℚ : is-emb real-ℚ
  is-emb-real-ℚ = is-emb-is-injective (is-set-ℝ lzero) is-injective-real-ℚ

  is-emb-real-ℚ⁺ : is-emb real-ℚ⁺
  is-emb-real-ℚ⁺ =
    is-emb-comp real-ℚ rational-ℚ⁺ is-emb-real-ℚ is-emb-rational-ℚ⁺

  is-emb-real-ℚ⁰⁺ : is-emb real-ℚ⁰⁺
  is-emb-real-ℚ⁰⁺ =
    is-emb-comp real-ℚ rational-ℚ⁰⁺ is-emb-real-ℚ is-emb-rational-ℚ⁰⁺

  is-emb-real-ℤ : is-emb real-ℤ
  is-emb-real-ℤ =
    is-emb-comp real-ℚ rational-ℤ is-emb-real-ℚ is-emb-rational-ℤ

  is-emb-real-ℕ : is-emb real-ℕ
  is-emb-real-ℕ =
    is-emb-comp real-ℤ int-ℕ is-emb-real-ℤ is-emb-int-ℕ

  is-injective-real-ℚ⁺ : is-injective real-ℚ⁺
  is-injective-real-ℚ⁺ = is-injective-is-emb is-emb-real-ℚ⁺

  is-injective-real-ℚ⁰⁺ : is-injective real-ℚ⁰⁺
  is-injective-real-ℚ⁰⁺ = is-injective-is-emb is-emb-real-ℚ⁰⁺

  is-injective-real-ℤ : is-injective real-ℤ
  is-injective-real-ℤ = is-injective-is-emb is-emb-real-ℤ

  is-injective-real-ℕ : is-injective real-ℕ
  is-injective-real-ℕ = is-injective-is-emb is-emb-real-ℕ
```

### `0 ≠ 1`

```agda
abstract
  neq-zero-one-ℝ : zero-ℝ ≠ one-ℝ
  neq-zero-one-ℝ = neq-zero-one-ℚ ∘ is-injective-real-ℚ

  neq-raise-zero-one-ℝ : (l : Level) → raise-zero-ℝ l ≠ raise-one-ℝ l
  neq-raise-zero-one-ℝ l 0=1ℝ =
    neq-zero-one-ℚ
      ( is-injective-real-ℚ
        ( eq-sim-ℝ
          ( similarity-reasoning-ℝ
              zero-ℝ
              ~ℝ raise-zero-ℝ l
                by sim-raise-ℝ l zero-ℝ
              ~ℝ raise-ℝ l one-ℝ
                by sim-eq-ℝ 0=1ℝ
              ~ℝ one-ℝ
                by sim-raise-ℝ' l one-ℝ)))
```
