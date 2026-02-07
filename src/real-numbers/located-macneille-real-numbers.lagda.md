# Located MacNeille real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.located-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.conjunction
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.embeddings
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.full-subtypes
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.macneille-real-numbers
```

</details>

## Idea

Every [Dedekind real](real-numbers.dedekind-real-numbers.md) determines a
[MacNeille real](real-numbers.macneille-real-numbers.md). Conversely, a
MacNeille real determines a Dedekind real provided its lower and upper cuts are
located. Therefore Dedekind reals coincide with located MacNeille reals.

## Definitions

### Located MacNeille reals

```agda
is-located-prop-macneille-ℝ : {l : Level} → subtype l (macneille-ℝ l)
is-located-prop-macneille-ℝ x =
  is-located-prop-lower-upper-ℝ
    ( lower-real-macneille-ℝ x)
    ( upper-real-macneille-ℝ x)

is-located-macneille-ℝ : {l : Level} → macneille-ℝ l → UU l
is-located-macneille-ℝ x =
  type-Prop (is-located-prop-macneille-ℝ x)

located-macneille-ℝ : (l : Level) → UU (lsuc l)
located-macneille-ℝ l = type-subtype is-located-prop-macneille-ℝ

is-set-located-macneille-ℝ : {l : Level} → is-set (located-macneille-ℝ l)
is-set-located-macneille-ℝ =
  is-set-type-subtype is-located-prop-macneille-ℝ is-set-macneille-ℝ
```

### Dedekind reals are MacNeille reals

```agda
module _
  {l : Level} (x : ℝ l)
  where

  is-open-upper-complement-lower-cut-real-ℝ :
    (q : ℚ) →
    is-in-upper-cut-ℝ x q ↔
    exists ℚ (λ p → le-ℚ-Prop p q ∧ ¬' lower-cut-ℝ x p)
  is-open-upper-complement-lower-cut-real-ℝ q =
    ( subset-upper-complement-lower-cut-upper-cut-ℝ x q ,
      subset-upper-cut-upper-complement-lower-cut-ℝ x q)

  is-open-lower-complement-upper-cut-real-ℝ :
    (p : ℚ) →
    is-in-lower-cut-ℝ x p ↔
    exists ℚ (λ q → le-ℚ-Prop p q ∧ ¬' upper-cut-ℝ x q)
  is-open-lower-complement-upper-cut-real-ℝ p =
    ( subset-lower-complement-upper-cut-lower-cut-ℝ x p ,
      subset-lower-cut-lower-complement-upper-cut-ℝ x p)

  is-open-dedekind-macneille-real-ℝ :
    is-open-dedekind-macneille-lower-upper-ℝ (lower-real-ℝ x) (upper-real-ℝ x)
  is-open-dedekind-macneille-real-ℝ =
    ( is-open-upper-complement-lower-cut-real-ℝ ,
      is-open-lower-complement-upper-cut-real-ℝ)

  macneille-real-ℝ : macneille-ℝ l
  macneille-real-ℝ =
    ( ( lower-real-ℝ x , upper-real-ℝ x) ,
      is-open-dedekind-macneille-real-ℝ)

  located-macneille-real-ℝ : located-macneille-ℝ l
  located-macneille-real-ℝ =
    ( macneille-real-ℝ , λ q r → is-located-lower-upper-cut-ℝ x)
```

### Located MacNeille reals are Dedekind reals

```agda
is-disjoint-lower-upper-real-macneille-ℝ :
  {l : Level} (x : macneille-ℝ l) →
  is-disjoint-lower-upper-ℝ
    ( lower-real-macneille-ℝ x)
    ( upper-real-macneille-ℝ x)
is-disjoint-lower-upper-real-macneille-ℝ x q (q∈L , q∈U) =
  is-not-in-upper-cut-is-in-lower-cut-macneille-ℝ x q q∈L q∈U

real-located-macneille-ℝ : {l : Level} → located-macneille-ℝ l → ℝ l
real-located-macneille-ℝ x =
  real-lower-upper-ℝ
    ( lower-real-macneille-ℝ (pr1 x))
    ( upper-real-macneille-ℝ (pr1 x))
    ( is-disjoint-lower-upper-real-macneille-ℝ (pr1 x))
    ( pr2 x)

real-macneille-ℝ :
  {l : Level} (x : macneille-ℝ l) →
  is-located-lower-upper-ℝ
    ( lower-real-macneille-ℝ x)
    ( upper-real-macneille-ℝ x) →
  ℝ l
real-macneille-ℝ x L = real-located-macneille-ℝ (x , L)
```

## Properties

### Located MacNeille reals are equivalent to Dedekind reals

```agda
abstract
  is-section-real-located-macneille-real-ℝ :
    {l : Level} →
    is-section (real-located-macneille-ℝ {l}) located-macneille-real-ℝ
  is-section-real-located-macneille-real-ℝ x =
    eq-eq-lower-real-ℝ
      ( real-located-macneille-ℝ (located-macneille-real-ℝ x))
      ( x)
      ( refl)

  is-retraction-real-located-macneille-real-ℝ :
    {l : Level} →
    is-retraction (real-located-macneille-ℝ {l}) located-macneille-real-ℝ
  is-retraction-real-located-macneille-real-ℝ {l} x =
    eq-type-subtype
      ( is-located-prop-macneille-ℝ)
      ( eq-macneille-ℝ
        ( macneille-real-ℝ (real-located-macneille-ℝ x))
        ( pr1 x)
        ( refl)
        ( refl))

  is-equiv-real-located-macneille-ℝ :
    {l : Level} → is-equiv (real-located-macneille-ℝ {l})
  is-equiv-real-located-macneille-ℝ =
    is-equiv-is-invertible
      ( located-macneille-real-ℝ)
      ( is-section-real-located-macneille-real-ℝ)
      ( is-retraction-real-located-macneille-real-ℝ)

  is-equiv-located-macneille-real-ℝ :
    {l : Level} → is-equiv (located-macneille-real-ℝ {l})
  is-equiv-located-macneille-real-ℝ =
    is-equiv-is-invertible
      ( real-located-macneille-ℝ)
      ( is-retraction-real-located-macneille-real-ℝ)
      ( is-section-real-located-macneille-real-ℝ)

equiv-located-macneille-ℝ : (l : Level) → located-macneille-ℝ l ≃ ℝ l
equiv-located-macneille-ℝ l =
  ( real-located-macneille-ℝ , is-equiv-real-located-macneille-ℝ)
```

### The map from Dedekind reals to MacNeille reals is an embedding

```agda
abstract
  is-emb-real-located-macneille-ℝ :
    {l : Level} → is-emb (real-located-macneille-ℝ {l})
  is-emb-real-located-macneille-ℝ =
    is-emb-is-equiv is-equiv-real-located-macneille-ℝ

  is-emb-located-macneille-real-ℝ :
    {l : Level} → is-emb (located-macneille-real-ℝ {l})
  is-emb-located-macneille-real-ℝ =
    is-emb-is-equiv is-equiv-located-macneille-real-ℝ

  is-emb-macneille-real-ℝ :
    {l : Level} → is-emb (macneille-real-ℝ {l})
  is-emb-macneille-real-ℝ {l} =
    is-emb-comp
      ( inclusion-subtype is-located-prop-macneille-ℝ)
      ( located-macneille-real-ℝ {l})
      ( is-emb-inclusion-subtype is-located-prop-macneille-ℝ)
      ( is-emb-located-macneille-real-ℝ {l})

  is-injective-macneille-real-ℝ :
    {l : Level} → is-injective (macneille-real-ℝ {l})
  is-injective-macneille-real-ℝ {l} =
    is-injective-is-emb (is-emb-macneille-real-ℝ {l})
```

### If all MacNeille reals are located, then they coincide with Dedekind reals

```agda
module _
  {l : Level} (L : (x : macneille-ℝ l) → is-located-macneille-ℝ x)
  where

  equiv-inclusion-located-all-macneille-located-ℝ :
    located-macneille-ℝ l ≃ macneille-ℝ l
  equiv-inclusion-located-all-macneille-located-ℝ =
    equiv-inclusion-is-full-subtype is-located-prop-macneille-ℝ L

  equiv-real-all-macneille-located-ℝ : macneille-ℝ l ≃ ℝ l
  equiv-real-all-macneille-located-ℝ =
    ( equiv-located-macneille-ℝ l) ∘e
    ( inv-equiv equiv-inclusion-located-all-macneille-located-ℝ)
```

### If the lower-cut is decidable then the MacNeille real is located

```agda
is-located-macneille-is-decidable-lower-cut-ℝ :
  {l : Level} (x : macneille-ℝ l) →
  ((p : ℚ) → is-decidable (is-in-lower-cut-macneille-ℝ x p)) →
  is-located-macneille-ℝ x
is-located-macneille-is-decidable-lower-cut-ℝ x D p q p<q =
  unit-trunc-Prop
    ( map-coproduct
      ( id)
      ( λ p∉L →
        backward-implication
          ( is-open-upper-complement-lower-cut-macneille-ℝ x q)
          ( intro-exists p (p<q , p∉L)))
      ( D p))

module _
  {l : Level}
  (D :
    (x : macneille-ℝ l) (p : ℚ) →
    is-decidable (is-in-lower-cut-macneille-ℝ x p))
  where

  equiv-macneille-is-decidable-lower-cut-ℝ : macneille-ℝ l ≃ ℝ l
  equiv-macneille-is-decidable-lower-cut-ℝ =
    equiv-real-all-macneille-located-ℝ
      ( λ x → is-located-macneille-is-decidable-lower-cut-ℝ x (D x))
```

### If the upper-cut is decidable then the MacNeille real is located

```agda
is-located-macneille-is-decidable-upper-cut-ℝ :
  {l : Level} (x : macneille-ℝ l) →
  ((p : ℚ) → is-decidable (is-in-upper-cut-macneille-ℝ x p)) →
  is-located-macneille-ℝ x
is-located-macneille-is-decidable-upper-cut-ℝ x D p q p<q =
  swap-disjunction
    ( unit-trunc-Prop
      ( map-coproduct
        ( id)
        ( λ q∉U →
          backward-implication
            ( is-open-lower-complement-upper-cut-macneille-ℝ x p)
            ( intro-exists q (p<q , q∉U)))
        ( D q)))

equiv-macneille-is-decidable-upper-cut-ℝ :
  {l : Level} →
  ( (x : macneille-ℝ l) (p : ℚ) →
    is-decidable (is-in-upper-cut-macneille-ℝ x p)) →
  macneille-ℝ l ≃ ℝ l
equiv-macneille-is-decidable-upper-cut-ℝ D =
  equiv-real-all-macneille-located-ℝ
    ( λ x → is-located-macneille-is-decidable-upper-cut-ℝ x (D x))
```

### Assuming excluded middle then every MacNeille real is located

```agda
module _
  {l : Level} (lem : level-LEM l)
  where

  is-decidable-lower-cut-macneille-ℝ-LEM :
    (x : macneille-ℝ l) (p : ℚ) →
    is-decidable (is-in-lower-cut-macneille-ℝ x p)
  is-decidable-lower-cut-macneille-ℝ-LEM x p =
    lem (lower-cut-macneille-ℝ x p)

  is-located-macneille-ℝ-LEM : (x : macneille-ℝ l) → is-located-macneille-ℝ x
  is-located-macneille-ℝ-LEM x =
    is-located-macneille-is-decidable-lower-cut-ℝ x
      ( is-decidable-lower-cut-macneille-ℝ-LEM x)

  equiv-macneille-ℝ-LEM : macneille-ℝ l ≃ ℝ l
  equiv-macneille-ℝ-LEM =
    equiv-real-all-macneille-located-ℝ is-located-macneille-ℝ-LEM
```
