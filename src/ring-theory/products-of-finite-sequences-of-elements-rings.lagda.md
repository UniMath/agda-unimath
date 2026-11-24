# Products of finite sequences of elements of rings

```agda
module ring-theory.products-of-finite-sequences-of-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.finite-sequences-in-rings

open import lists.finite-sequences

open import ring-theory.products-of-finite-sequences-of-elements-semirings
open import ring-theory.rings
```

</details>

## Idea

The
{{#concept "product operation" Disambiguation="over finite sequences in a ring" Agda=product-fin-sequence-type-Ring}}
extends the binary multiplication operation on a [ring](ring-theory.rings.md)
`R` to any [finite sequence](lists.finite-sequences.md) of elements of `R`.

## Definition

```agda
product-fin-sequence-type-Ring :
  {l : Level} (R : Ring l) (n : ℕ) →
  fin-sequence-type-Ring R n → type-Ring R
product-fin-sequence-type-Ring R =
  product-fin-sequence-type-Semiring (semiring-Ring R)
```
