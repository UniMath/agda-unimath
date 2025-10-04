# Negation of closed intervals in the rational numbers

```agda
module elementary-number-theory.negation-closed-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.interior-closed-intervals-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.dependent-pair-types
```

</details>

## Idea

The {{#concept "negation" Disambiguation="closed interval of rational numbers" Agda=neg-closed-interval-ℚ}} of a
[closed interval of rational numbers](elementary-number-theory.closed-intervals-rational-numbers.md)
[a, b] is [-b, -a].

## Definition

```agda
neg-closed-interval-ℚ : closed-interval-ℚ → closed-interval-ℚ
neg-closed-interval-ℚ ((a , b) , a≤b) =
  ((neg-ℚ b , neg-ℚ a) , neg-leq-ℚ a b a≤b)
```

## Properties

### Negation preserves interior intervals

```agda
abstract
  is-interior-neg-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    is-interior-closed-interval-ℚ [a,b] [c,d] →
    is-interior-closed-interval-ℚ
      ( neg-closed-interval-ℚ [a,b])
      ( neg-closed-interval-ℚ [c,d])
  is-interior-neg-closed-interval-ℚ ((a , b) , _) ((c , d) , _) (a<c , d<b) =
    ( neg-le-ℚ d b d<b , neg-le-ℚ a c a<c)
```

### Negation preserves nontriviality

```agda
abstract
  is-nontrivial-neg-closed-interval-ℚ :
    ([a,b] : closed-interval-ℚ) → is-proper-closed-interval-ℚ [a,b] →
    is-proper-closed-interval-ℚ (neg-closed-interval-ℚ [a,b])
  is-nontrivial-neg-closed-interval-ℚ ((a , b) , _) a<b = neg-le-ℚ a b a<b
```
