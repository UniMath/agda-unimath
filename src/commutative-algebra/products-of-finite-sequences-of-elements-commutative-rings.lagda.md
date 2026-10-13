# Products of finite sequences of elements of commutative rings

```agda
module commutative-algebra.products-of-finite-sequences-of-elements-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.finite-sequences-in-commutative-rings

open import lists.finite-sequences

open import ring-theory.products-of-finite-sequences-of-elements-rings
```

</details>

## Idea

The
{{#concept "product operation" Disambiguation="over finite sequences in a commutative ring" Agda=product-fin-sequence-type-Commutative-Ring}}
extends the binary multiplication operation on a
[commutative ring](commutative-algebra.commutative-rings.md) `R` to any
[finite sequence](lists.finite-sequences.md) of elements of `R`.

## Definition

```agda
product-fin-sequence-type-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) (n : ℕ) →
  fin-sequence-type-Commutative-Ring R n → type-Commutative-Ring R
product-fin-sequence-type-Commutative-Ring R =
  product-fin-sequence-type-Ring (ring-Commutative-Ring R)
```
