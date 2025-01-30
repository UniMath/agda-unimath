# Addition on the natural numbers

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
```

</details>

## Definition

```agda
abstract
  archimedean-property-ℕ :
    (x : nonzero-ℕ) →
      (y : ℕ) →
      Σ ℕ (λ n → le-ℕ y (n *ℕ nat-nonzero-ℕ x))
  archimedean-property-ℕ (x , nonzero-x) y =
    (succ-ℕ (quotient-euclidean-division-ℕ x y) , {!   !})
```
