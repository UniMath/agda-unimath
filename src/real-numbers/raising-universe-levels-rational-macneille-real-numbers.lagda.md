# Raising universe Levels of rational MacNeille real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.raising-universe-levels-rational-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.universe-levels

open import real-numbers.inequality-lower-dedekind-real-numbers
open import real-numbers.inequality-macneille-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.raising-universe-levels-macneille-real-numbers
open import real-numbers.rational-macneille-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-macneille-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

For every [universe](foundation.universe-levels.md) `𝒰` there is a type of
[rational MacNeille real numbers](real-numbers.rational-macneille-real-numbers.md)
relative to `𝒰`. Given a larger universe `𝒱`, then we may
{{#concept "raise" Disambiguation="a rational MacNeille real number"}} a
rational MacNeille real number `x` from the universe `𝒰` to a
[similar](real-numbers.similarity-macneille-real-numbers.md) rational MacNeille
real number in the universe `𝒱`.

## Properties

### Raising universe levels preserves order

```agda
abstract opaque
  unfolding real-ℚ

  leq-raise-macneille-real-ℚ :
    {l : Level} (p q : ℚ) → leq-ℚ p q →
    leq-macneille-ℝ (raise-macneille-real-ℚ l p) (raise-macneille-real-ℚ l q)
  leq-raise-macneille-real-ℚ {l} p q p≤q =
    ( ( λ r r<p →
        map-raise (preserves-leq-lower-real-ℚ p q p≤q r (map-inv-raise r<p))) ,
      ( leq-upper-leq-lower-real-macneille-ℝ
        ( raise-macneille-real-ℚ l p)
        ( raise-macneille-real-ℚ l q)
        ( λ r r<p →
          map-raise
            ( preserves-leq-lower-real-ℚ p q p≤q r (map-inv-raise r<p)))))
```

### Raising universe levels preserves strict order

```agda
abstract opaque
  unfolding le-macneille-ℝ

  le-raise-macneille-real-ℚ :
    {l : Level} (p q : ℚ) → le-ℚ p q →
    le-macneille-ℝ (raise-macneille-real-ℚ l p) (raise-macneille-real-ℚ l q)
  le-raise-macneille-real-ℚ {l} p q p<q =
    map-trunc-Prop
      ( λ (r , p<r , r<q) →
        ( r ,
          map-raise
            ( is-in-upper-cut-le-real-ℚ (real-ℚ p) (preserves-le-real-ℚ p<r)) ,
          map-raise
            ( is-in-lower-cut-le-real-ℚ (real-ℚ q) (preserves-le-real-ℚ r<q))))
      ( dense-le-ℚ p<q)

  reflects-le-raise-macneille-real-ℚ :
    {l : Level} (p q : ℚ) →
    le-macneille-ℝ (raise-macneille-real-ℚ l p) (raise-macneille-real-ℚ l q) →
    le-ℚ p q
  reflects-le-raise-macneille-real-ℚ {l} p q =
    elim-exists
      ( le-ℚ-Prop p q)
      ( λ r (p<r , r<q) →
        transitive-le-ℚ p r q
          ( reflects-le-real-ℚ
            ( le-real-is-in-lower-cut-ℝ (real-ℚ q) (map-inv-raise r<q)))
          ( reflects-le-real-ℚ
            ( le-real-is-in-upper-cut-ℝ (real-ℚ p) (map-inv-raise p<r))))
```

### Raising universe levels reflects strict order

```agda
abstract opaque
  unfolding le-macneille-ℝ

  reflects-le-left-raise-macneille-real-ℚ :
    {l : Level} (p q : ℚ) →
    le-macneille-ℝ (raise-macneille-real-ℚ l p) (macneille-real-ℚ q) →
    le-ℚ p q
  reflects-le-left-raise-macneille-real-ℚ {l} p q =
    elim-exists
      ( le-ℚ-Prop p q)
      ( λ r (p<r , r<q) →
        transitive-le-ℚ p r q
          ( reflects-le-macneille-real-ℚ
            ( le-real-is-in-lower-cut-macneille-ℝ (macneille-real-ℚ q) r<q))
          ( reflects-le-real-ℚ
            ( le-real-is-in-upper-cut-ℝ (real-ℚ p) (map-inv-raise p<r))))
```
