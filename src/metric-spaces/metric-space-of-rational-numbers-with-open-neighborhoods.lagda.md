# The metric structure on the rational numbers with open neighborhoods

```agda
{-# OPTIONS --lossy-unification #-}
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module metric-spaces.metric-space-of-rational-numbers-with-open-neighborhoods
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers funext univalence truncations
open import elementary-number-theory.difference-rational-numbers funext univalence truncations
open import elementary-number-theory.inequality-rational-numbers funext univalence truncations
open import elementary-number-theory.positive-rational-numbers funext univalence truncations
open import elementary-number-theory.rational-numbers funext univalence truncations
open import elementary-number-theory.strict-inequality-rational-numbers funext univalence truncations

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types funext univalence
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.empty-types funext univalence truncations
open import foundation.equivalences funext
open import foundation.function-types funext
open import foundation.identity-types funext
open import foundation.propositions funext univalence
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.extensional-premetric-structures funext univalence truncations
open import metric-spaces.metric-spaces funext univalence truncations
open import metric-spaces.metric-structures funext univalence truncations
open import metric-spaces.monotonic-premetric-structures funext univalence truncations
open import metric-spaces.premetric-spaces funext univalence truncations
open import metric-spaces.premetric-structures funext univalence truncations
open import metric-spaces.pseudometric-structures funext univalence truncations
open import metric-spaces.reflexive-premetric-structures funext univalence truncations
open import metric-spaces.symmetric-premetric-structures funext univalence truncations
open import metric-spaces.triangular-premetric-structures funext univalence truncations
```

</details>

## Idea

[Srict inequality](elementary-number-theory.strict-inequality-rational-numbers.md)
on the [rational numbers](elementary-number-theory.rational-numbers.md) induces
a [premetric](metric-spaces.premetric-structures.md) on `ℚ` where `x y : ℚ` are
in a `d`-neighborhood when `y < x + d` and `x < y + d`, i.e. upper bounds on the
distance between `x` and `y` are strict upper bounds of both `y - x` and
`x - y`. This is a [metric structure](metric-spaces.metric-structures.md) on `ℚ`
that defines the
{{#concept "standard metric space of rational numbers with open neighborhoods" Agda=metric-space-le-ℚ}}.

## Definitions

### The standard premetric on the rational numbers with open neighborhoods

```agda
premetric-le-ℚ : Premetric lzero ℚ
premetric-le-ℚ d x y =
  product-Prop
    ( le-ℚ-Prop y (x +ℚ (rational-ℚ⁺ d)))
    ( le-ℚ-Prop x (y +ℚ (rational-ℚ⁺ d)))
```

## Properties

### The standard premetric on the rational numbers is a metric

```agda
is-reflexive-premetric-le-ℚ : is-reflexive-Premetric premetric-le-ℚ
is-reflexive-premetric-le-ℚ d x =
  (le-right-add-rational-ℚ⁺ x d , le-right-add-rational-ℚ⁺ x d)

is-symmetric-premetric-le-ℚ : is-symmetric-Premetric premetric-le-ℚ
is-symmetric-premetric-le-ℚ d x y (H , K) = (K , H)

is-tight-premetric-le-ℚ : is-tight-Premetric premetric-le-ℚ
is-tight-premetric-le-ℚ x y H =
  antisymmetric-leq-ℚ
    ( x)
    ( y)
    ( map-inv-equiv (equiv-leq-le-add-positive-ℚ x y) (pr2 ∘ H))
    ( map-inv-equiv (equiv-leq-le-add-positive-ℚ y x) (pr1 ∘ H))

is-local-premetric-le-ℚ : is-local-Premetric premetric-le-ℚ
is-local-premetric-le-ℚ =
  is-local-is-tight-Premetric
    premetric-le-ℚ
    is-tight-premetric-le-ℚ

is-triangular-premetric-le-ℚ :
  is-triangular-Premetric premetric-le-ℚ
pr1 (is-triangular-premetric-le-ℚ x y z d₁ d₂ Hyz Hxy) =
  tr
    ( le-ℚ z)
    ( associative-add-ℚ x (rational-ℚ⁺ d₁) (rational-ℚ⁺ d₂))
    ( transitive-le-ℚ
      ( z)
      ( y +ℚ ( rational-ℚ⁺ d₂))
      ( x +ℚ (rational-ℚ⁺ d₁) +ℚ (rational-ℚ⁺ d₂))
      ( preserves-le-left-add-ℚ
        ( rational-ℚ⁺ d₂)
        ( y)
        ( x +ℚ (rational-ℚ⁺ d₁))
        ( pr1 Hxy))
      ( pr1 Hyz))
pr2 (is-triangular-premetric-le-ℚ x y z d₁ d₂ Hyz Hxy) =
  tr
    ( le-ℚ x)
    ( ap (z +ℚ_) (commutative-add-ℚ (rational-ℚ⁺ d₂) (rational-ℚ⁺ d₁)))
    ( tr
      ( le-ℚ x)
      ( associative-add-ℚ z (rational-ℚ⁺ d₂) (rational-ℚ⁺ d₁))
      ( transitive-le-ℚ
        ( x)
        ( y +ℚ (rational-ℚ⁺ d₁))
        ( z +ℚ (rational-ℚ⁺ d₂) +ℚ (rational-ℚ⁺ d₁))
        ( ( preserves-le-left-add-ℚ
          ( rational-ℚ⁺ d₁)
          ( y)
          ( z +ℚ (rational-ℚ⁺ d₂))
          ( pr2 Hyz)))
        ( pr2 Hxy)))

is-pseudometric-premetric-le-ℚ : is-pseudometric-Premetric premetric-le-ℚ
is-pseudometric-premetric-le-ℚ =
  is-reflexive-premetric-le-ℚ ,
  is-symmetric-premetric-le-ℚ ,
  is-triangular-premetric-le-ℚ

is-metric-premetric-le-ℚ : is-metric-Premetric premetric-le-ℚ
pr1 is-metric-premetric-le-ℚ = is-pseudometric-premetric-le-ℚ
pr2 is-metric-premetric-le-ℚ = is-local-premetric-le-ℚ
```

### The standard metric space of rational numbers with open neighborhoods

```agda
premetric-space-le-ℚ : Premetric-Space lzero lzero
premetric-space-le-ℚ = ℚ , premetric-le-ℚ

metric-space-le-ℚ : Metric-Space lzero lzero
pr1 metric-space-le-ℚ = premetric-space-le-ℚ
pr2 metric-space-le-ℚ = is-metric-premetric-le-ℚ
```

## See also

- The standard
  [metric space of rational numbers](metric-spaces.metric-space-of-rational-numbers.md)
