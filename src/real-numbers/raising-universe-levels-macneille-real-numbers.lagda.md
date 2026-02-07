# Raising the universe levels of MacNeille real numbers

```agda
module real-numbers.raising-universe-levels-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.raising-universe-levels-lower-dedekind-real-numbers
open import real-numbers.raising-universe-levels-upper-dedekind-real-numbers
open import real-numbers.similarity-macneille-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

For every [universe](foundation.universe-levels.md) `𝒰` there is a type of
[MacNeille real numbers](real-numbers.macneille-real-numbers.md) `ℝₘ` relative
to `𝒰`, `ℝₘ 𝒰`. Given a larger universe `𝒱`, then we may
{{#concept "raise" Disambiguation="a MacNeille real number" Agda=raise-macneille-ℝ}}
a MacNeille real number `x` from the universe `𝒰` to a
[similar](real-numbers.similarity-macneille-real-numbers.md) MacNeille real
number in the universe `𝒱`.

## Definitions

### Raising MacNeille real numbers

```agda
module _
  {l0 : Level} (l : Level) (x : macneille-ℝ l0)
  where

  lower-real-raise-macneille-ℝ : lower-ℝ (l0 ⊔ l)
  lower-real-raise-macneille-ℝ = raise-lower-ℝ l (lower-real-macneille-ℝ x)

  upper-real-raise-macneille-ℝ : upper-ℝ (l0 ⊔ l)
  upper-real-raise-macneille-ℝ = raise-upper-ℝ l (upper-real-macneille-ℝ x)

  abstract
    is-disjoint-cut-raise-macneille-ℝ :
      (q : ℚ) →
      ¬ ( is-in-cut-lower-ℝ lower-real-raise-macneille-ℝ q ×
          is-in-cut-upper-ℝ upper-real-raise-macneille-ℝ q)
    is-disjoint-cut-raise-macneille-ℝ q (map-raise q<x , map-raise x<q) =
      is-disjoint-cut-macneille-ℝ x q (q<x , x<q)

    forward-open-upper-complement-lower-cut-raise-macneille-ℝ :
      (q : ℚ) →
      is-in-cut-upper-ℝ upper-real-raise-macneille-ℝ q →
      exists ℚ
        ( λ p →
          le-ℚ-Prop p q ∧
          ¬' cut-lower-ℝ lower-real-raise-macneille-ℝ p)
    forward-open-upper-complement-lower-cut-raise-macneille-ℝ
      q (map-raise x<q) =
      map-tot-exists
        ( λ _ → map-product id (map-neg map-inv-raise))
        ( forward-implication
          ( is-open-upper-complement-lower-cut-macneille-ℝ x q)
          ( x<q))

    backward-open-upper-complement-lower-cut-raise-macneille-ℝ :
      (q : ℚ) →
      exists ℚ
        ( λ p →
          le-ℚ-Prop p q ∧
          ¬' cut-lower-ℝ lower-real-raise-macneille-ℝ p) →
      is-in-cut-upper-ℝ upper-real-raise-macneille-ℝ q
    backward-open-upper-complement-lower-cut-raise-macneille-ℝ q ∃p =
      map-raise
        ( backward-implication
          ( is-open-upper-complement-lower-cut-macneille-ℝ x q)
          ( map-tot-exists
            ( λ _ → map-product id (map-neg map-raise))
            ( ∃p)))

    is-open-upper-complement-lower-cut-raise-macneille-ℝ :
      (q : ℚ) →
      is-in-cut-upper-ℝ upper-real-raise-macneille-ℝ q ↔
      exists ℚ
        ( λ p →
          le-ℚ-Prop p q ∧
          ¬' cut-lower-ℝ lower-real-raise-macneille-ℝ p)
    is-open-upper-complement-lower-cut-raise-macneille-ℝ q =
      ( forward-open-upper-complement-lower-cut-raise-macneille-ℝ q ,
        backward-open-upper-complement-lower-cut-raise-macneille-ℝ q)

    forward-open-lower-complement-upper-cut-raise-macneille-ℝ :
      (p : ℚ) →
      is-in-cut-lower-ℝ lower-real-raise-macneille-ℝ p →
      exists ℚ
        ( λ q →
          le-ℚ-Prop p q ∧
          ¬' cut-upper-ℝ upper-real-raise-macneille-ℝ q)
    forward-open-lower-complement-upper-cut-raise-macneille-ℝ
      p (map-raise p<x) =
      map-tot-exists
        ( λ _ → map-product id (map-neg map-inv-raise))
        ( forward-implication
          ( is-open-lower-complement-upper-cut-macneille-ℝ x p)
          ( p<x))

    backward-open-lower-complement-upper-cut-raise-macneille-ℝ :
      (p : ℚ) →
      exists ℚ
        ( λ q →
          le-ℚ-Prop p q ∧
          ¬' cut-upper-ℝ upper-real-raise-macneille-ℝ q) →
      is-in-cut-lower-ℝ lower-real-raise-macneille-ℝ p
    backward-open-lower-complement-upper-cut-raise-macneille-ℝ p ∃q =
      map-raise
        ( backward-implication
          ( is-open-lower-complement-upper-cut-macneille-ℝ x p)
          ( map-tot-exists
            ( λ _ → map-product id (map-neg map-raise))
            ( ∃q)))

    is-open-lower-complement-upper-cut-raise-macneille-ℝ :
      (p : ℚ) →
      is-in-cut-lower-ℝ lower-real-raise-macneille-ℝ p ↔
      exists ℚ
        ( λ q →
          le-ℚ-Prop p q ∧
          ¬' cut-upper-ℝ upper-real-raise-macneille-ℝ q)
    is-open-lower-complement-upper-cut-raise-macneille-ℝ p =
      ( forward-open-lower-complement-upper-cut-raise-macneille-ℝ p ,
        backward-open-lower-complement-upper-cut-raise-macneille-ℝ p)

  raise-macneille-ℝ : macneille-ℝ (l0 ⊔ l)
  raise-macneille-ℝ =
    ( ( lower-real-raise-macneille-ℝ , upper-real-raise-macneille-ℝ) ,
      ( is-open-upper-complement-lower-cut-raise-macneille-ℝ ,
        is-open-lower-complement-upper-cut-raise-macneille-ℝ))
```

## Properties

### MacNeille reals are similar to their raised-universe equivalents

```agda
abstract opaque
  unfolding sim-macneille-ℝ

  sim-raise-macneille-ℝ :
    {l0 : Level} (l : Level) (x : macneille-ℝ l0) →
    sim-macneille-ℝ x (raise-macneille-ℝ l x)
  pr1 (sim-raise-macneille-ℝ l x) _ = map-raise
  pr2 (sim-raise-macneille-ℝ l x) _ = map-inv-raise

abstract
  sim-raise-macneille-ℝ' :
    {l0 : Level} (l : Level) (x : macneille-ℝ l0) →
    sim-macneille-ℝ (raise-macneille-ℝ l x) x
  sim-raise-macneille-ℝ' l x =
    symmetric-sim-macneille-ℝ (sim-raise-macneille-ℝ l x)

  sim-raise-raise-macneille-ℝ :
    {l0 : Level} (l1 l2 : Level) (x : macneille-ℝ l0) →
    sim-macneille-ℝ (raise-macneille-ℝ l1 x) (raise-macneille-ℝ l2 x)
  sim-raise-raise-macneille-ℝ l1 l2 x =
    transitive-sim-macneille-ℝ _ _ _
      ( sim-raise-macneille-ℝ l2 x)
      ( sim-raise-macneille-ℝ' l1 x)
```

### Raising a MacNeille real to its own level is the identity

```agda
eq-raise-macneille-ℝ :
  {l : Level} (x : macneille-ℝ l) → x ＝ raise-macneille-ℝ l x
eq-raise-macneille-ℝ {l} x =
  eq-sim-macneille-ℝ (sim-raise-macneille-ℝ l x)
```

### `x` and `y` are similar if and only if `x` raised to `y`'s universe level equals `y` raised to `x`'s universe level

```agda
module _
  {l1 l2 : Level}
  {x : macneille-ℝ l1}
  {y : macneille-ℝ l2}
  where

  abstract
    eq-raise-sim-macneille-ℝ :
      sim-macneille-ℝ x y →
      raise-macneille-ℝ l2 x ＝ raise-macneille-ℝ l1 y
    eq-raise-sim-macneille-ℝ x~y =
      eq-sim-macneille-ℝ
        ( similarity-reasoning-macneille-ℝ
          raise-macneille-ℝ l2 x
          ~ℝₘ x
            by sim-raise-macneille-ℝ' l2 x
          ~ℝₘ y
            by x~y
          ~ℝₘ raise-macneille-ℝ l1 y
            by sim-raise-macneille-ℝ l1 y)

    sim-eq-raise-macneille-ℝ :
      raise-macneille-ℝ l2 x ＝ raise-macneille-ℝ l1 y → sim-macneille-ℝ x y
    sim-eq-raise-macneille-ℝ l2x=l1y =
      similarity-reasoning-macneille-ℝ
        x
        ~ℝₘ raise-macneille-ℝ l2 x
          by sim-raise-macneille-ℝ l2 x
        ~ℝₘ raise-macneille-ℝ l1 y
          by sim-eq-macneille-ℝ l2x=l1y
        ~ℝₘ y
          by sim-raise-macneille-ℝ' l1 y
```

### Raising a real by two universe levels is equivalent to raising by the least upper bound of the universe levels

```agda
abstract
  raise-raise-macneille-ℝ :
    {l1 l2 l3 : Level} (x : macneille-ℝ l1) →
    raise-macneille-ℝ l2 (raise-macneille-ℝ l3 x) ＝
    raise-macneille-ℝ (l2 ⊔ l3) x
  raise-raise-macneille-ℝ {l1} {l2} {l3} x =
    eq-sim-macneille-ℝ
      ( similarity-reasoning-macneille-ℝ
        raise-macneille-ℝ l2 (raise-macneille-ℝ l3 x)
        ~ℝₘ raise-macneille-ℝ l3 x
          by sim-raise-macneille-ℝ' l2 _
        ~ℝₘ raise-macneille-ℝ (l2 ⊔ l3) x
          by sim-raise-raise-macneille-ℝ l3 (l2 ⊔ l3) x)
```
