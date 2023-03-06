# Retracts of the type of natural numbers

<details><summary>Imports</summary>
```agda
module elementary-number-theory.retracts-of-natural-numbers where
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers
open import foundation.decidable-maps
open import foundation.retractions
open import foundation.universe-levels
```
</details>

## Idea

If `i : A → ℕ` has a retraction, then `i` is a decidable map.

```agda
is-decidable-map-retr-ℕ :
  {l1 : Level} {A : UU l1} (i : A → ℕ) → retr i → is-decidable-map i
is-decidable-map-retr-ℕ =
  is-decidable-map-retr has-decidable-equality-ℕ
```
