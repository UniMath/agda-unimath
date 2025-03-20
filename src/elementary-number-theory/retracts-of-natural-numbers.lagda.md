# Retracts of the type of natural numbers

```agda
open import foundation.function-extensionality-axiom

module
  elementary-number-theory.retracts-of-natural-numbers
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers funext
open import elementary-number-theory.natural-numbers

open import foundation.decidable-maps funext
open import foundation.retractions funext
open import foundation.universe-levels
```

</details>

## Idea

If `i : A → ℕ` has a retraction, then `i` is a decidable map.

```agda
is-decidable-map-retraction-ℕ :
  {l1 : Level} {A : UU l1} (i : A → ℕ) → retraction i → is-decidable-map i
is-decidable-map-retraction-ℕ =
  is-decidable-map-retraction has-decidable-equality-ℕ
```
