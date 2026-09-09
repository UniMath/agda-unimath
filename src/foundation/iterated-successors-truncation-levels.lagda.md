# Iterated successors of truncation levels

```agda
module foundation.iterated-successors-truncation-levels where

open import foundation-core.iterated-successors-truncation-levels public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.truncation-levels

open import foundation-core.identity-types
```

</details>

## Properties

### Coherence with addition on natural numbers

```agda
add+2-truncation-level-minus-one-ℕ :
  (k n : ℕ) →
  truncation-level-minus-one-ℕ (k +ℕ n) ＝
  add+2-𝕋
    ( truncation-level-minus-one-ℕ k)
    ( truncation-level-minus-two-ℕ n)
add+2-truncation-level-minus-one-ℕ k zero-ℕ = refl
add+2-truncation-level-minus-one-ℕ k (succ-ℕ n) =
  ap succ-𝕋 (add+2-truncation-level-minus-one-ℕ k n)
```
