# The Archimedean property of the natural numbers

```agda
module elementary-number-theory.archimedean-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.euclidean-division-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.dependent-pair-types
open import foundation.transport-along-identifications
```

</details>

## Definition

The Archimedean property of the natural numbers is that for any nonzero natural
number `x` and natural number `y`, there is an `n : ℕ` such that `y < n *ℕ x`.

```agda
abstract
  archimedean-property-ℕ :
    (x y : ℕ) → is-nonzero-ℕ x → Σ ℕ (λ n → le-ℕ y (n *ℕ x))
  archimedean-property-ℕ x y nonzero-x =
    (succ-ℕ (quotient-euclidean-division-ℕ x y) ,
      tr
        (λ z → le-ℕ z (succ-ℕ (quotient-euclidean-division-ℕ x y) *ℕ x))
        (eq-euclidean-division-ℕ x y)
        (preserves-le-left-add-ℕ
          (quotient-euclidean-division-ℕ x y *ℕ x)
          (remainder-euclidean-division-ℕ x y)
          x
          (strict-upper-bound-remainder-euclidean-division-ℕ x y nonzero-x)))
```

## External links

- [Archimedean property](https://en.wikipedia.org/wiki/Archimedean_property) at
  Wikipedia
