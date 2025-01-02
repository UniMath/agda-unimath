# Parity of the natural numbers

```agda
module elementary-number-theory.parity-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.euclidean-division-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.identity-types
open import foundation.negation
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

{{#concept "Parity" WD="parity" WDID=Q141160}}
[partitions](foundation.partitions.md) the [natural
numbers](elementary-number-theory.natural numbers.md) into two
[classes](foundation.equivalence-relations.md): the
{{#concept "even" Disambiguation="natural number" Agda=is-even-ℕ WD="even number" WDID=Q13366104}}
and the
{{#concept "odd" Disambiguation="natural number" Agda=is-odd-ℕ WD="odd number" WDID=Q13366129}}
natural numbers. Even natural numbers are those that are
[divisible](elementary-number-theory.divisibility-natural numbers.md) by two,
and odd natural numbers are those that aren't.

## Definition

### Even natural numbers

```agda
is-even-ℕ : ℕ → UU lzero
is-even-ℕ n = div-ℕ 2 n
```

### The sequence of even numbers

```agda
even-number-ℕ : ℕ → ℕ
even-number-ℕ n = 2 *ℕ n
```

### Odd natural numbers

```agda
is-odd-ℕ : ℕ → UU lzero
is-odd-ℕ n = ¬ (is-even-ℕ n)
```

### The sequence of odd numbers

```agda
odd-number-ℕ : ℕ → ℕ
odd-number-ℕ n = succ-ℕ (2 *ℕ n)
```

### The predicate of having an odd expansion

```agda
has-odd-expansion-ℕ : ℕ → UU lzero
has-odd-expansion-ℕ n = fiber odd-number-ℕ n
```

## Properties

### The `n`th even number is even

```agda
is-even-even-number-ℕ :
  (n : ℕ) → is-even-ℕ (even-number-ℕ n)
pr1 (is-even-even-number-ℕ n) = n
pr2 (is-even-even-number-ℕ n) = commutative-mul-ℕ n 2
```

### Even natural numbers are closed under equality

```agda
is-even-eq-ℕ : {m n : ℕ} → m ＝ n → is-even-ℕ n → is-even-ℕ m
is-even-eq-ℕ refl H = H

is-even-eq-ℕ' : {m n : ℕ} → m ＝ n → is-even-ℕ m → is-even-ℕ n
is-even-eq-ℕ' refl H = H
```

### Odd natural numbers are closed under equality

```agda
is-odd-eq-ℕ : {m n : ℕ} → m ＝ n → is-odd-ℕ n → is-odd-ℕ m
is-odd-eq-ℕ refl H = H

is-odd-eq-ℕ' : {m n : ℕ} → m ＝ n → is-odd-ℕ m → is-odd-ℕ n
is-odd-eq-ℕ' refl H = H
```

### Being even or odd is decidable

```agda
is-decidable-is-even-ℕ : (x : ℕ) → is-decidable (is-even-ℕ x)
is-decidable-is-even-ℕ x = is-decidable-div-ℕ 2 x

is-decidable-is-odd-ℕ : (x : ℕ) → is-decidable (is-odd-ℕ x)
is-decidable-is-odd-ℕ x = is-decidable-neg (is-decidable-is-even-ℕ x)
```

### A number is even if and only if it is not odd

```agda
is-even-is-not-odd-ℕ : (x : ℕ) → ¬ (is-odd-ℕ x) → is-even-ℕ x
is-even-is-not-odd-ℕ x =
  double-negation-elim-is-decidable (is-decidable-is-even-ℕ x)

is-not-odd-is-even-ℕ : (x : ℕ) → is-even-ℕ x → ¬ (is-odd-ℕ x)
is-not-odd-is-even-ℕ x = intro-double-negation
```

### `0` is an even natural number

```agda
is-even-zero-ℕ : is-even-ℕ 0
is-even-zero-ℕ = div-zero-ℕ 2
```

### `1` is an odd natural number

```agda
is-odd-one-ℕ : is-odd-ℕ 1
is-odd-one-ℕ H = Eq-eq-ℕ (is-one-div-one-ℕ 2 H)
```

### A natural number `x` is even if and only if `x + 2` is even

```agda
is-even-is-even-succ-succ-ℕ :
  (n : ℕ) → is-even-ℕ (succ-ℕ (succ-ℕ n)) → is-even-ℕ n
pr1 (is-even-is-even-succ-succ-ℕ n (succ-ℕ d , p)) = d
pr2 (is-even-is-even-succ-succ-ℕ n (succ-ℕ d , p)) =
  is-injective-succ-ℕ (is-injective-succ-ℕ p)

is-even-succ-succ-is-even-ℕ :
  (n : ℕ) → is-even-ℕ n → is-even-ℕ (succ-ℕ (succ-ℕ n))
pr1 (is-even-succ-succ-is-even-ℕ n (d , p)) = succ-ℕ d
pr2 (is-even-succ-succ-is-even-ℕ n (d , p)) = ap (succ-ℕ ∘ succ-ℕ) p
```

### A natural number `x` is odd if and only if `x + 2` is odd

```agda
is-odd-is-odd-succ-succ-ℕ :
  (n : ℕ) → is-odd-ℕ (succ-ℕ (succ-ℕ n)) → is-odd-ℕ n
is-odd-is-odd-succ-succ-ℕ n = map-neg (is-even-succ-succ-is-even-ℕ n)

is-odd-succ-succ-is-odd-ℕ :
  (n : ℕ) → is-odd-ℕ n → is-odd-ℕ (succ-ℕ (succ-ℕ n))
is-odd-succ-succ-is-odd-ℕ n = map-neg (is-even-is-even-succ-succ-ℕ n)
```

### If a natural number `x` is odd, then `x + 1` is even

```agda
is-even-succ-is-odd-ℕ :
  (n : ℕ) → is-odd-ℕ n → is-even-ℕ (succ-ℕ n)
is-even-succ-is-odd-ℕ zero-ℕ p = ex-falso (p is-even-zero-ℕ)
is-even-succ-is-odd-ℕ (succ-ℕ zero-ℕ) p = (1 , refl)
is-even-succ-is-odd-ℕ (succ-ℕ (succ-ℕ n)) p =
  is-even-succ-succ-is-even-ℕ
    ( succ-ℕ n)
    ( is-even-succ-is-odd-ℕ n (is-odd-is-odd-succ-succ-ℕ n p))
```

### If a natural number `x` is even, then `x + 1` is odd

```agda
is-odd-succ-is-even-ℕ :
  (n : ℕ) → is-even-ℕ n → is-odd-ℕ (succ-ℕ n)
is-odd-succ-is-even-ℕ zero-ℕ p = is-odd-one-ℕ
is-odd-succ-is-even-ℕ (succ-ℕ zero-ℕ) p = ex-falso (is-odd-one-ℕ p)
is-odd-succ-is-even-ℕ (succ-ℕ (succ-ℕ n)) p =
  is-odd-succ-succ-is-odd-ℕ
    ( succ-ℕ n)
    ( is-odd-succ-is-even-ℕ n (is-even-is-even-succ-succ-ℕ n p))
```

### If a natural number `x + 1` is odd, then `x` is even

```agda
is-even-is-odd-succ-ℕ :
  (n : ℕ) → is-odd-ℕ (succ-ℕ n) → is-even-ℕ n
is-even-is-odd-succ-ℕ n p =
  is-even-is-even-succ-succ-ℕ
    ( n)
    ( is-even-succ-is-odd-ℕ (succ-ℕ n) p)
```

### If a natural number `x + 1` is even, then `x` is odd

```agda
is-odd-is-even-succ-ℕ :
  (n : ℕ) → is-even-ℕ (succ-ℕ n) → is-odd-ℕ n
is-odd-is-even-succ-ℕ n p =
  is-odd-is-odd-succ-succ-ℕ
    ( n)
    ( is-odd-succ-is-even-ℕ (succ-ℕ n) p)
```

### A natural number is odd if and only if it has an odd expansion

```agda
is-odd-has-odd-expansion-ℕ : (n : ℕ) → has-odd-expansion-ℕ n → is-odd-ℕ n
is-odd-has-odd-expansion-ℕ .(succ-ℕ (2 *ℕ m)) (m , refl) =
  is-odd-succ-is-even-ℕ (2 *ℕ m) (m , commutative-mul-ℕ m 2)

has-odd-expansion-is-odd-ℕ : (n : ℕ) → is-odd-ℕ n → has-odd-expansion-ℕ n
has-odd-expansion-is-odd-ℕ zero-ℕ p = ex-falso (p is-even-zero-ℕ)
has-odd-expansion-is-odd-ℕ (succ-ℕ zero-ℕ) p = (0 , refl)
has-odd-expansion-is-odd-ℕ (succ-ℕ (succ-ℕ n)) p =
  ( succ-ℕ (pr1 s)) ,
    ap (succ-ℕ ∘ succ-ℕ) (left-successor-law-add-ℕ _ _ ∙ pr2 s)
  where
  s : has-odd-expansion-ℕ n
  s = has-odd-expansion-is-odd-ℕ n (is-odd-is-odd-succ-succ-ℕ n p)
```

### A number is even if and only if it is divisible by an even number

```agda
is-even-div-is-even-ℕ :
  (n m : ℕ) → is-even-ℕ m → div-ℕ m n → is-even-ℕ n
is-even-div-is-even-ℕ ._ ._ (m' , refl) (k , refl) =
  k *ℕ m' , associative-mul-ℕ k m' 2

is-even-div-4-ℕ :
  (n : ℕ) → div-ℕ 4 n → is-even-ℕ n
is-even-div-4-ℕ n = is-even-div-is-even-ℕ n 4 (2 , refl)
```

### A number is even if and only if it is congruent to `0` modulo `2`

```agda
is-0-mod-2-is-even-ℕ :
  (n : ℕ) → is-even-ℕ n → n ≡ 0 mod-ℕ 2
is-0-mod-2-is-even-ℕ =
  cong-zero-div-ℕ 2

is-even-is-0-mod-2-ℕ :
  (n : ℕ) → n ≡ 0 mod-ℕ 2 → is-even-ℕ n
is-even-is-0-mod-2-ℕ =
  div-cong-zero-ℕ 2
```

### A natural number is odd if and only if it is congruent to `1` modulo `2`

```agda
is-1-mod-2-has-odd-expansion-ℕ :
  (n : ℕ) → has-odd-expansion-ℕ n → n ≡ 1 mod-ℕ 2
is-1-mod-2-has-odd-expansion-ℕ ._ (k , refl) =
  translation-invariant-cong-ℕ' 2
    ( 2 *ℕ k)
    ( 0)
    ( 1)
    ( is-0-mod-2-is-even-ℕ
      ( 2 *ℕ k)
      ( is-even-even-number-ℕ k ))

is-1-mod-2-is-odd-ℕ :
  (n : ℕ) → is-odd-ℕ n → n ≡ 1 mod-ℕ 2
is-1-mod-2-is-odd-ℕ n H =
  is-1-mod-2-has-odd-expansion-ℕ n (has-odd-expansion-is-odd-ℕ n H)

is-odd-is-1-mod-2-ℕ :
  (n : ℕ) → n ≡ 1 mod-ℕ 2 → is-odd-ℕ n
is-odd-is-1-mod-2-ℕ zero-ℕ H K =
  is-not-one-two-ℕ (is-one-div-one-ℕ 2 H)
is-odd-is-1-mod-2-ℕ (succ-ℕ n) H K =
  is-odd-one-ℕ
    ( div-right-summand-ℕ 2 n 1 (tr (div-ℕ 2) (right-unit-law-dist-ℕ n) H) K)
```

### If any two out of `x`, `y`, and `x + y` are even, then so is the third

```agda
is-even-add-ℕ :
  (m n : ℕ) → is-even-ℕ m → is-even-ℕ n → is-even-ℕ (add-ℕ m n)
is-even-add-ℕ = div-add-ℕ 2

is-even-left-summand-ℕ :
  (m n : ℕ) → is-even-ℕ n → is-even-ℕ (add-ℕ m n) → is-even-ℕ m
is-even-left-summand-ℕ = div-left-summand-ℕ 2

is-even-right-summand-ℕ :
  (m n : ℕ) → is-even-ℕ m → is-even-ℕ (add-ℕ m n) → is-even-ℕ n
is-even-right-summand-ℕ = div-right-summand-ℕ 2
```

### If any two out of `x`, `y`, and `x + y` are odd, then the third number is even

```agda
is-even-add-is-odd-ℕ :
  (m n : ℕ) → is-odd-ℕ m → is-odd-ℕ n → is-even-ℕ (m +ℕ n)
is-even-add-is-odd-ℕ m zero-ℕ H K = ex-falso (K is-even-zero-ℕ)
is-even-add-is-odd-ℕ m (succ-ℕ zero-ℕ) H K =
  is-even-succ-is-odd-ℕ m H
is-even-add-is-odd-ℕ m (succ-ℕ (succ-ℕ n)) H K =
  is-even-succ-succ-is-even-ℕ
    ( add-ℕ m n)
    ( is-even-add-is-odd-ℕ m n H (is-odd-is-odd-succ-succ-ℕ n K))

is-even-left-summand-is-odd-ℕ :
  (m n : ℕ) → is-odd-ℕ n → is-odd-ℕ (m +ℕ n) → is-even-ℕ m
is-even-left-summand-is-odd-ℕ m zero-ℕ H K = ex-falso (H is-even-zero-ℕ)
is-even-left-summand-is-odd-ℕ m (succ-ℕ zero-ℕ) H K =
  is-even-is-odd-succ-ℕ m K
is-even-left-summand-is-odd-ℕ m (succ-ℕ (succ-ℕ n)) H K =
  is-even-left-summand-is-odd-ℕ m n
    ( is-odd-is-odd-succ-succ-ℕ n H)
    ( is-odd-is-odd-succ-succ-ℕ (m +ℕ n) K)

is-even-right-summand-is-odd-ℕ :
  (m n : ℕ) → is-odd-ℕ m → is-odd-ℕ (m +ℕ n) → is-even-ℕ n
is-even-right-summand-is-odd-ℕ m zero-ℕ H K = is-even-zero-ℕ
is-even-right-summand-is-odd-ℕ m (succ-ℕ zero-ℕ) H K =
  ex-falso (K (is-even-succ-is-odd-ℕ m H))
is-even-right-summand-is-odd-ℕ m (succ-ℕ (succ-ℕ n)) H K =
  is-even-succ-succ-is-even-ℕ n
    ( is-even-right-summand-is-odd-ℕ m n H
      ( is-odd-is-odd-succ-succ-ℕ (m +ℕ n) K))
```

### If one of the summands is even and the other is odd, then the sum is odd

```agda
is-odd-add-is-odd-left-summand-ℕ :
  (m n : ℕ) → is-odd-ℕ m → is-even-ℕ n → is-odd-ℕ (m +ℕ n)
is-odd-add-is-odd-left-summand-ℕ m n H K L =
  H (is-even-left-summand-ℕ m n K L)

is-odd-add-is-odd-right-summand-ℕ :
  (m n : ℕ) → is-even-ℕ m → is-odd-ℕ n → is-odd-ℕ (m +ℕ n)
is-odd-add-is-odd-right-summand-ℕ m n H K L =
  K (is-even-right-summand-ℕ m n H L)
```

### Either `n` or `n + 1` is even

```agda
abstract
  is-even-or-is-even-succ-ℕ :
    (n : ℕ) → is-even-ℕ n + is-even-ℕ (succ-ℕ n)
  is-even-or-is-even-succ-ℕ n
    with
    is-decidable-is-even-ℕ n
  ... | inl H = inl H
  ... | inr H = inr (is-even-succ-is-odd-ℕ n H)
```

### Either `n` or `n + 1` is odd

```agda
abstract
  is-odd-or-is-odd-succ-ℕ :
    (n : ℕ) → is-odd-ℕ n + is-odd-ℕ (succ-ℕ n)
  is-odd-or-is-odd-succ-ℕ n
    with
    is-decidable-is-odd-ℕ n
  ... | inl H = inl H
  ... | inr H = inr (is-odd-succ-is-even-ℕ n (is-even-is-not-odd-ℕ n H))
```

### The sum `n + n` is even

```agda
is-even-add-self-ℕ : (n : ℕ) → is-even-ℕ (n +ℕ n)
is-even-add-self-ℕ n = (n , right-two-law-mul-ℕ n)
```

### The sum `n + (n + 1)` is odd

```agda
is-odd-add-succ-self-ℕ :
  (n : ℕ) → is-odd-ℕ (n +ℕ succ-ℕ n)
is-odd-add-succ-self-ℕ n =
  is-odd-succ-is-even-ℕ (n +ℕ n) (is-even-add-self-ℕ n)
```

### The product `n(n + 1)` is even

```agda
abstract
  is-even-mul-succ-ℕ :
    (n : ℕ) → is-even-ℕ (n *ℕ succ-ℕ n)
  is-even-mul-succ-ℕ n
    with is-even-or-is-even-succ-ℕ n
  ... | inl H =
    is-even-div-is-even-ℕ
      ( n *ℕ succ-ℕ n)
      ( n)
      ( H)
      ( succ-ℕ n , commutative-mul-ℕ (succ-ℕ n) n)
  ... | inr H =
    is-even-div-is-even-ℕ
      ( n *ℕ succ-ℕ n)
      ( succ-ℕ n)
      ( H)
      ( n , refl)
```

## See also

Further laws of parity are proven in other files, e.g.:

- [Parity of integers](elementary-number-theory.parity-integers.md)
- [Squares of natural numbers](elementary-number-theory.squares-natural-numbers.md)
