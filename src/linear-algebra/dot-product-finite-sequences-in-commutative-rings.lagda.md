# The dot product of finite sequences in commutative rings

```agda
module linear-algebra.dot-product-finite-sequences-in-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.dot-product-finite-sequences-in-rings
open import linear-algebra.finite-sequences-in-commutative-rings
```

</details>

## Idea

The
{{#concept "dot product" Disambiguation="of finite sequences in commutative rings" Agda=dot-product-fin-sequence-type-Commutative-Ring}}
of two
[finite sequences](linear-algebra.finite-sequences-in-commutative-rings.md) `u`
and `v` in a [commutative](commutative-algebra.commutative-rings.md) is the
[sum](commutative-algebra.sums-of-finite-sequences-of-elements-commutative-rings.md)
`∑ᵢ uᵢvᵢ`.

## Definition

```agda
dot-product-fin-sequence-type-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) (n : ℕ) →
  fin-sequence-type-Commutative-Ring R n →
  fin-sequence-type-Commutative-Ring R n →
  type-Commutative-Ring R
dot-product-fin-sequence-type-Commutative-Ring R =
  dot-product-fin-sequence-type-Ring (ring-Commutative-Ring R)
```

## Properties

### The dot product is symmetric

```agda
abstract
  symmetric-dot-product-fin-sequence-type-Commutative-Ring :
    {l : Level} (R : Commutative-Ring l) (n : ℕ)
    (u v : fin-sequence-type-Commutative-Ring R n) →
    dot-product-fin-sequence-type-Commutative-Ring R n u v ＝
    dot-product-fin-sequence-type-Commutative-Ring R n v u
  symmetric-dot-product-fin-sequence-type-Commutative-Ring R n u v =
    htpy-sum-fin-sequence-type-Commutative-Ring R n
      ( λ i → commutative-mul-Commutative-Ring R (u i) (v i))
```
