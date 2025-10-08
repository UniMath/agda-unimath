# The binomial coefficients

```agda
module elementary-number-theory.binomial-coefficients where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.factorials
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.semiring-of-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "binomial coefficient" WD="binomial coefficient" WDID=Q209875 Agda=binomial-coefficient-ℕ}}
`(n choose k)` measures
[how many decidable subsets](univalent-combinatorics.counting-decidable-subtypes.md)
of size `k` there are of a
[finite type](univalent-combinatorics.finite-types.md) of size `n`.

## Definition

### Binomial coefficients of natural numbers

```agda
binomial-coefficient-ℕ : ℕ → ℕ → ℕ
binomial-coefficient-ℕ zero-ℕ zero-ℕ = 1
binomial-coefficient-ℕ zero-ℕ (succ-ℕ k) = 0
binomial-coefficient-ℕ (succ-ℕ n) zero-ℕ = 1
binomial-coefficient-ℕ (succ-ℕ n) (succ-ℕ k) =
  (binomial-coefficient-ℕ n k) +ℕ (binomial-coefficient-ℕ n (succ-ℕ k))
```

### Binomial coefficients indexed by elements of standard finite types

```agda
binomial-coefficient-Fin : (n : ℕ) → Fin (succ-ℕ n) → ℕ
binomial-coefficient-Fin n x = binomial-coefficient-ℕ n (nat-Fin (succ-ℕ n) x)
```

## Properties

### If `k > n` then `binomial-coefficient-ℕ n k ＝ 0`

```agda
is-zero-binomial-coefficient-ℕ :
  (n k : ℕ) → le-ℕ n k → is-zero-ℕ (binomial-coefficient-ℕ n k)
is-zero-binomial-coefficient-ℕ zero-ℕ (succ-ℕ k) _ = refl
is-zero-binomial-coefficient-ℕ (succ-ℕ n) (succ-ℕ k) H =
  ap-add-ℕ
    ( is-zero-binomial-coefficient-ℕ n k H)
    ( is-zero-binomial-coefficient-ℕ n (succ-ℕ k) (preserves-le-succ-ℕ n k H))
```

### `binomial-coefficient-ℕ n n ＝ 1`

```agda
is-one-on-diagonal-binomial-coefficient-ℕ :
  (n : ℕ) → is-one-ℕ (binomial-coefficient-ℕ n n)
is-one-on-diagonal-binomial-coefficient-ℕ zero-ℕ = refl
is-one-on-diagonal-binomial-coefficient-ℕ (succ-ℕ n) =
  ap-add-ℕ
    ( is-one-on-diagonal-binomial-coefficient-ℕ n)
    ( is-zero-binomial-coefficient-ℕ n (succ-ℕ n) (succ-le-ℕ n))
```

### For all `k, l : ℕ`, `binomial-coefficient-ℕ (k + l) k *ℕ (factorial-ℕ k *ℕ factorial-ℕ l) ＝ factorial-ℕ (k + l)`

```agda
abstract
  binomial-coefficient-factorial-formula-ℕ :
    (k l : ℕ) →
    binomial-coefficient-ℕ (k +ℕ l) k *ℕ (factorial-ℕ k *ℕ factorial-ℕ l) ＝
    factorial-ℕ (k +ℕ l)
  binomial-coefficient-factorial-formula-ℕ k zero-ℕ =
    ap-mul-ℕ
      ( is-one-on-diagonal-binomial-coefficient-ℕ k)
      ( right-unit-law-mul-ℕ (factorial-ℕ k)) ∙
    left-unit-law-mul-ℕ (factorial-ℕ k)
  binomial-coefficient-factorial-formula-ℕ zero-ℕ (succ-ℕ l) =
    left-unit-law-mul-ℕ (1 *ℕ factorial-ℕ (succ-ℕ l)) ∙
    left-unit-law-mul-ℕ (factorial-ℕ (succ-ℕ l)) ∙
    ap factorial-ℕ (inv (left-unit-law-add-ℕ (succ-ℕ l)))
  binomial-coefficient-factorial-formula-ℕ (succ-ℕ k) (succ-ℕ l) =
    equational-reasoning
      ( binomial-coefficient-ℕ (succ-ℕ k +ℕ l) k +ℕ
        binomial-coefficient-ℕ (succ-ℕ k +ℕ l) (succ-ℕ k)) *ℕ
      ( factorial-ℕ (succ-ℕ k) *ℕ factorial-ℕ (succ-ℕ l))
      ＝ ( ( binomial-coefficient-ℕ (succ-ℕ k +ℕ l) k) *ℕ
          ( (factorial-ℕ k *ℕ succ-ℕ k) *ℕ factorial-ℕ (succ-ℕ l))) +ℕ
        ( ( binomial-coefficient-ℕ (succ-ℕ k +ℕ l) (succ-ℕ k)) *ℕ
          ( factorial-ℕ (succ-ℕ k) *ℕ (factorial-ℕ l *ℕ succ-ℕ l)))
        by
        right-distributive-mul-add-ℕ
          ( binomial-coefficient-ℕ (succ-ℕ k +ℕ l) k)
          ( binomial-coefficient-ℕ (succ-ℕ k +ℕ l) (succ-ℕ k))
          ( factorial-ℕ (succ-ℕ k) *ℕ factorial-ℕ (succ-ℕ l))
      ＝ ( ( binomial-coefficient-ℕ (succ-ℕ k +ℕ l) k) *ℕ
          ( (factorial-ℕ k *ℕ factorial-ℕ (succ-ℕ l)) *ℕ succ-ℕ k)) +ℕ
        ( ( binomial-coefficient-ℕ (succ-ℕ k +ℕ l) (succ-ℕ k)) *ℕ
          ( (factorial-ℕ (succ-ℕ k) *ℕ factorial-ℕ l) *ℕ succ-ℕ l))
          by
          ap-add-ℕ
            ( ap
              ( binomial-coefficient-ℕ (succ-ℕ k +ℕ l) k *ℕ_)
              ( right-swap-mul-Commutative-Semiring
                ( ℕ-Commutative-Semiring)
                ( factorial-ℕ k)
                ( succ-ℕ k)
                ( factorial-ℕ (succ-ℕ l))))
            ( ap
              ( binomial-coefficient-ℕ (succ-ℕ k +ℕ l) (succ-ℕ k) *ℕ_)
              ( inv
                ( associative-mul-ℕ
                  ( factorial-ℕ (succ-ℕ k))
                  ( factorial-ℕ l)
                  ( succ-ℕ l))))
      ＝ ( ( binomial-coefficient-ℕ (k +ℕ succ-ℕ l) k) *ℕ
          ( (factorial-ℕ k *ℕ factorial-ℕ (succ-ℕ l)) *ℕ succ-ℕ k)) +ℕ
        ( ( binomial-coefficient-ℕ (succ-ℕ k +ℕ l) (succ-ℕ k)) *ℕ
          ( (factorial-ℕ (succ-ℕ k) *ℕ factorial-ℕ l) *ℕ succ-ℕ l))
        by
        ap
          ( λ a →
            ( ( binomial-coefficient-ℕ a k) *ℕ
              ( (factorial-ℕ k *ℕ factorial-ℕ (succ-ℕ l)) *ℕ succ-ℕ k)) +ℕ
            ( ( binomial-coefficient-ℕ (succ-ℕ k +ℕ l) (succ-ℕ k)) *ℕ
              ( (factorial-ℕ (succ-ℕ k) *ℕ factorial-ℕ l) *ℕ succ-ℕ l)))
          ( left-successor-law-add-ℕ k l ∙ inv (right-successor-law-add-ℕ k l))
      ＝ ( ( ( binomial-coefficient-ℕ (k +ℕ succ-ℕ l) k) *ℕ
            ( factorial-ℕ k *ℕ factorial-ℕ (succ-ℕ l))) *ℕ
            ( succ-ℕ k)) +ℕ
        ( ( ( binomial-coefficient-ℕ (succ-ℕ k +ℕ l) (succ-ℕ k)) *ℕ
            ( factorial-ℕ (succ-ℕ k) *ℕ factorial-ℕ l)) *ℕ
          ( succ-ℕ l))
        by
        ap-add-ℕ
          ( inv
            ( associative-mul-ℕ
              ( binomial-coefficient-ℕ (k +ℕ succ-ℕ l) k)
              ( factorial-ℕ k *ℕ factorial-ℕ (succ-ℕ l))
              ( succ-ℕ k)))
          ( inv
            ( associative-mul-ℕ
              ( binomial-coefficient-ℕ (succ-ℕ k +ℕ l) (succ-ℕ k))
              ( factorial-ℕ (succ-ℕ k) *ℕ factorial-ℕ l)
              ( succ-ℕ l)))
      ＝ ( factorial-ℕ (k +ℕ succ-ℕ l) *ℕ succ-ℕ k) +ℕ
        ( factorial-ℕ (succ-ℕ k +ℕ l) *ℕ succ-ℕ l)
        by
        ap-add-ℕ
          ( ap
            ( _*ℕ succ-ℕ k)
            ( binomial-coefficient-factorial-formula-ℕ k (succ-ℕ l)))
          ( ap
            ( _*ℕ succ-ℕ l)
            ( binomial-coefficient-factorial-formula-ℕ (succ-ℕ k) l))
      ＝ ( factorial-ℕ (succ-ℕ k +ℕ l) *ℕ succ-ℕ k) +ℕ
        ( factorial-ℕ (succ-ℕ k +ℕ l) *ℕ succ-ℕ l)
        by
        ap
          ( λ a →
            ( factorial-ℕ a *ℕ succ-ℕ k) +ℕ
            ( factorial-ℕ (succ-ℕ k +ℕ l) *ℕ succ-ℕ l))
          ( right-successor-law-add-ℕ k l ∙ inv (left-successor-law-add-ℕ k l))
      ＝ factorial-ℕ (succ-ℕ k +ℕ succ-ℕ l)
        by
        inv
          ( left-distributive-mul-add-ℕ
            ( factorial-ℕ (succ-ℕ k +ℕ l))
            ( succ-ℕ k)
            ( succ-ℕ l))
```

### `binomial-coefficient-ℕ (k + l) k ＝ binomial-coefficient-ℕ (k + l) l`

```agda
abstract
  binomial-coefficient-symmetric-ℕ :
    (k l : ℕ) →
    binomial-coefficient-ℕ (k +ℕ l) k ＝ binomial-coefficient-ℕ (k +ℕ l) l
  binomial-coefficient-symmetric-ℕ k l =
    is-injective-right-mul-ℕ
      ( factorial-ℕ k *ℕ factorial-ℕ l)
      ( is-nonzero-mul-ℕ
        ( factorial-ℕ k)
        ( factorial-ℕ l)
        ( is-nonzero-factorial-ℕ k)
        ( is-nonzero-factorial-ℕ l))
      ( equational-reasoning
        binomial-coefficient-ℕ (k +ℕ l) k *ℕ (factorial-ℕ k *ℕ factorial-ℕ l)
        ＝ factorial-ℕ (k +ℕ l)
          by
          binomial-coefficient-factorial-formula-ℕ k l
        ＝ factorial-ℕ (l +ℕ k)
          by
          ap factorial-ℕ (commutative-add-ℕ k l)
        ＝ binomial-coefficient-ℕ (l +ℕ k) l *ℕ (factorial-ℕ l *ℕ factorial-ℕ k)
          by
          inv (binomial-coefficient-factorial-formula-ℕ l k)
        ＝ binomial-coefficient-ℕ (l +ℕ k) l *ℕ (factorial-ℕ k *ℕ factorial-ℕ l)
          by
          ap
            ( binomial-coefficient-ℕ (l +ℕ k) l *ℕ_)
            ( commutative-mul-ℕ (factorial-ℕ l) (factorial-ℕ k))
        ＝ binomial-coefficient-ℕ (k +ℕ l) l *ℕ (factorial-ℕ k *ℕ factorial-ℕ l)
          by
          ap
            ( λ a →
              binomial-coefficient-ℕ a l *ℕ (factorial-ℕ k *ℕ factorial-ℕ l))
            ( commutative-add-ℕ l k))
```

## See also

- [Binomial types](univalent-combinatorics.binomial-types.md)

## External links

- [Binomial coefficients](https://www.britannica.com/science/binomial-coefficient)
  at Britannica
- [Binomial coefficient](https://en.wikipedia.org/wiki/Binomial_coefficient) at
  Wikipedia
- [Binomial Coefficient](https://mathworld.wolfram.com/BinomialCoefficient.html)
  at Wolfram MathWorld
