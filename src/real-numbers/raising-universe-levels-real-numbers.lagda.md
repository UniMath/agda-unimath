# Raising the universe levels of real numbers

```agda
module real-numbers.raising-universe-levels-real-numbers where
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

open import real-numbers.dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.raising-universe-levels-lower-dedekind-real-numbers
open import real-numbers.raising-universe-levels-upper-dedekind-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

For every [universe](foundation.universe-levels.md) `𝒰` there is a type of
[real numbers](real-numbers.dedekind-real-numbers.md) `ℝ` relative to `𝒰`,
`ℝ 𝒰`. Given a larger universe `𝒱`, then we may
{{#concept "raise" Disambiguation="a Dedekind real number" Agda=raise-ℝ}} a real
number `x` from the universe `𝒰` to a
[similar](real-numbers.similarity-real-numbers.md) real number in the universe
`𝒱`.

## Definitions

### Raising Dedekind real numbers

```agda
module _
  {l0 : Level} (l : Level) (x : ℝ l0)
  where

  lower-real-raise-ℝ : lower-ℝ (l0 ⊔ l)
  lower-real-raise-ℝ = raise-lower-ℝ l (lower-real-ℝ x)

  upper-real-raise-ℝ : upper-ℝ (l0 ⊔ l)
  upper-real-raise-ℝ = raise-upper-ℝ l (upper-real-ℝ x)

  abstract
    is-disjoint-cut-raise-ℝ :
      (q : ℚ) →
      ¬
        ( is-in-cut-lower-ℝ lower-real-raise-ℝ q ×
          is-in-cut-upper-ℝ upper-real-raise-ℝ q)
    is-disjoint-cut-raise-ℝ q (map-raise q<x , map-raise x<q) =
      is-disjoint-cut-ℝ x q (q<x , x<q)

    is-located-lower-upper-cut-raise-ℝ :
      (p q : ℚ) → le-ℚ p q →
      type-disjunction-Prop
        ( cut-lower-ℝ lower-real-raise-ℝ p)
        ( cut-upper-ℝ upper-real-raise-ℝ q)
    is-located-lower-upper-cut-raise-ℝ p q p<q =
      map-disjunction
        ( map-raise)
        ( map-raise)
        ( is-located-lower-upper-cut-ℝ x p<q)

  raise-ℝ : ℝ (l0 ⊔ l)
  raise-ℝ =
    real-lower-upper-ℝ
      ( lower-real-raise-ℝ)
      ( upper-real-raise-ℝ)
      ( is-disjoint-cut-raise-ℝ)
      ( is-located-lower-upper-cut-raise-ℝ)
```

## Properties

### Reals are similar to their raised-universe equivalents

```agda
abstract opaque
  unfolding sim-ℝ

  sim-raise-ℝ : {l0 : Level} (l : Level) (x : ℝ l0) → sim-ℝ x (raise-ℝ l x)
  pr1 (sim-raise-ℝ l x) _ = map-raise
  pr2 (sim-raise-ℝ l x) _ = map-inv-raise

abstract
  sim-raise-ℝ' : {l0 : Level} (l : Level) (x : ℝ l0) → sim-ℝ (raise-ℝ l x) x
  sim-raise-ℝ' l x = symmetric-sim-ℝ (sim-raise-ℝ l x)

  sim-raise-raise-ℝ :
    {l0 : Level} (l1 l2 : Level) (x : ℝ l0) →
    sim-ℝ (raise-ℝ l1 x) (raise-ℝ l2 x)
  sim-raise-raise-ℝ l1 l2 x =
    transitive-sim-ℝ _ _ _ (sim-raise-ℝ l2 x) (sim-raise-ℝ' l1 x)
```

### Raising a real to its own level is the identity

```agda
eq-raise-ℝ : {l : Level} (x : ℝ l) → x ＝ raise-ℝ l x
eq-raise-ℝ {l} x = eq-sim-ℝ (sim-raise-ℝ l x)
```

### `x` and `y` are similar if and only if `x` raised to `y`'s universe level equals `y` raised to `x`'s universe level

```agda
module _
  {l1 l2 : Level}
  {x : ℝ l1}
  {y : ℝ l2}
  where

  abstract
    eq-raise-sim-ℝ : sim-ℝ x y → raise-ℝ l2 x ＝ raise-ℝ l1 y
    eq-raise-sim-ℝ x~y =
      eq-sim-ℝ
        ( similarity-reasoning-ℝ
          raise-ℝ l2 x
          ~ℝ x
            by sim-raise-ℝ' l2 x
          ~ℝ y
            by x~y
          ~ℝ raise-ℝ l1 y
            by sim-raise-ℝ l1 y)

    sim-eq-raise-ℝ : raise-ℝ l2 x ＝ raise-ℝ l1 y → sim-ℝ x y
    sim-eq-raise-ℝ l2x=l1y =
      similarity-reasoning-ℝ
        x
        ~ℝ raise-ℝ l2 x
          by sim-raise-ℝ l2 x
        ~ℝ raise-ℝ l1 y
          by sim-eq-ℝ l2x=l1y
        ~ℝ y
          by sim-raise-ℝ' l1 y
```

### Raising a real by two universe levels is equivalent to raising by the least upper bound of the universe levels

```agda
abstract
  raise-raise-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) →
    raise-ℝ l2 (raise-ℝ l3 x) ＝ raise-ℝ (l2 ⊔ l3) x
  raise-raise-ℝ {l1} {l2} {l3} x =
    eq-sim-ℝ
      ( similarity-reasoning-ℝ
        raise-ℝ l2 (raise-ℝ l3 x)
        ~ℝ raise-ℝ l3 x
          by sim-raise-ℝ' l2 _
        ~ℝ raise-ℝ (l2 ⊔ l3) x
          by sim-raise-raise-ℝ l3 (l2 ⊔ l3) x)
```
