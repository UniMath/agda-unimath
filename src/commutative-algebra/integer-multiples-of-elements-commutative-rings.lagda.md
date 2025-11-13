# Integer multiples of elements of commutative rings

```agda
module commutative-algebra.integer-multiples-of-elements-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.homomorphisms-commutative-rings
open import commutative-algebra.multiples-of-elements-commutative-rings

open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.homomorphisms-abelian-groups

open import ring-theory.integer-multiples-of-elements-rings
```

</details>

## Idea

The **integer multiple operation** on a
[commutative ring](commutative-algebra.commutative-rings.md) is the map
`k x ↦ kx`, which is defined by
[iteratively](foundation.iterating-automorphisms.md) adding `x` with itself an
[integer](elementary-number-theory.integers.md) `k` times.

## Definitions

### Iteratively adding `g`

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  iterative-addition-by-element-Commutative-Ring :
    type-Commutative-Ring A →
    ℤ → type-Commutative-Ring A → type-Commutative-Ring A
  iterative-addition-by-element-Commutative-Ring =
    iterative-addition-by-element-Ring (ring-Commutative-Ring A)
```

### Integer multiples of elements of commutative rings

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  integer-multiple-Commutative-Ring :
    ℤ → type-Commutative-Ring A → type-Commutative-Ring A
  integer-multiple-Commutative-Ring =
    integer-multiple-Ring (ring-Commutative-Ring A)
```

## Properties

### Associativity of iterated addition by an element of a commutative ring

```agda
module _
  {l : Level} (A : Commutative-Ring l) (a : type-Commutative-Ring A)
  where

  associative-iterative-addition-by-element-Commutative-Ring :
    (k : ℤ) (h1 h2 : type-Commutative-Ring A) →
    iterative-addition-by-element-Commutative-Ring A a k
      ( add-Commutative-Ring A h1 h2) ＝
    add-Commutative-Ring A
      ( iterative-addition-by-element-Commutative-Ring A a k h1)
      ( h2)
  associative-iterative-addition-by-element-Commutative-Ring =
    associative-iterative-addition-by-element-Ring (ring-Commutative-Ring A) a
```

### `integer-multiple-Commutative-Ring A (int-ℕ n) a ＝ multiple-Commutative-Ring A n a`

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  integer-multiple-int-Commutative-Ring :
    (n : ℕ) (a : type-Commutative-Ring A) →
    integer-multiple-Commutative-Ring A (int-ℕ n) a ＝
    multiple-Commutative-Ring A n a
  integer-multiple-int-Commutative-Ring =
    integer-multiple-int-Ring (ring-Commutative-Ring A)

  integer-multiple-in-pos-Commutative-Ring :
    (n : ℕ) (a : type-Commutative-Ring A) →
    integer-multiple-Commutative-Ring A (in-pos-ℤ n) a ＝
    multiple-Commutative-Ring A (succ-ℕ n) a
  integer-multiple-in-pos-Commutative-Ring =
    integer-multiple-in-pos-Ring (ring-Commutative-Ring A)

  integer-multiple-in-neg-Commutative-Ring :
    (n : ℕ) (a : type-Commutative-Ring A) →
    integer-multiple-Commutative-Ring A (in-neg-ℤ n) a ＝
    neg-Commutative-Ring A (multiple-Commutative-Ring A (succ-ℕ n) a)
  integer-multiple-in-neg-Commutative-Ring =
    integer-multiple-in-neg-Ring (ring-Commutative-Ring A)
```

### The integer multiple `0x` is `0`

```agda
module _
  {l : Level} (A : Commutative-Ring l) (a : type-Commutative-Ring A)
  where

  integer-right-zero-law-multiple-Commutative-Ring :
    integer-multiple-Commutative-Ring A zero-ℤ a ＝ zero-Commutative-Ring A
  integer-right-zero-law-multiple-Commutative-Ring =
    integer-right-zero-law-multiple-Ring (ring-Commutative-Ring A) a
```

### `1x ＝ x`

```agda
module _
  {l : Level} (A : Commutative-Ring l) (a : type-Commutative-Ring A)
  where

  integer-multiple-one-Commutative-Ring :
    integer-multiple-Commutative-Ring A one-ℤ a ＝ a
  integer-multiple-one-Commutative-Ring =
    integer-multiple-one-Ring (ring-Commutative-Ring A) a
```

### The integer multiple `(-1)x` is the negative of `x`

```agda
module _
  {l : Level} (A : Commutative-Ring l) (a : type-Commutative-Ring A)
  where

  integer-multiple-neg-one-Commutative-Ring :
    integer-multiple-Commutative-Ring A neg-one-ℤ a ＝ neg-Commutative-Ring A a
  integer-multiple-neg-one-Commutative-Ring =
    integer-multiple-neg-one-Ring (ring-Commutative-Ring A) a
```

### The integer multiple `(x + y)a` computes to `xa + ya`

```agda
module _
  {l : Level} (A : Commutative-Ring l) (a : type-Commutative-Ring A)
  where

  distributive-integer-multiple-add-Commutative-Ring :
    (x y : ℤ) →
    integer-multiple-Commutative-Ring A (x +ℤ y) a ＝
    add-Commutative-Ring A
      ( integer-multiple-Commutative-Ring A x a)
      ( integer-multiple-Commutative-Ring A y a)
  distributive-integer-multiple-add-Commutative-Ring =
    distributive-integer-multiple-add-Ring (ring-Commutative-Ring A) a
```

### The integer multiple `(-k)x` is the negative of the integer multiple `kx`

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  integer-multiple-neg-Commutative-Ring :
    (k : ℤ) (x : type-Commutative-Ring A) →
    integer-multiple-Commutative-Ring A (neg-ℤ k) x ＝
    neg-Commutative-Ring A (integer-multiple-Commutative-Ring A k x)
  integer-multiple-neg-Commutative-Ring =
    integer-multiple-neg-Ring (ring-Commutative-Ring A)
```

### `(k + 1)x = kx + x` and `(k+1)x = x + kx`

```agda
module _
  {l1 : Level} (A : Commutative-Ring l1)
  where

  integer-multiple-succ-Commutative-Ring :
    (k : ℤ) (x : type-Commutative-Ring A) →
    integer-multiple-Commutative-Ring A (succ-ℤ k) x ＝
    add-Commutative-Ring A (integer-multiple-Commutative-Ring A k x) x
  integer-multiple-succ-Commutative-Ring =
    integer-multiple-succ-Ring (ring-Commutative-Ring A)

  integer-multiple-succ-Commutative-Ring' :
    (k : ℤ) (x : type-Commutative-Ring A) →
    integer-multiple-Commutative-Ring A (succ-ℤ k) x ＝
    add-Commutative-Ring A x (integer-multiple-Commutative-Ring A k x)
  integer-multiple-succ-Commutative-Ring' =
    integer-multiple-succ-Ring' (ring-Commutative-Ring A)
```

### `(k - 1)x = kx - x` and `(k - 1)x = -x + kx`

```agda
module _
  {l1 : Level} (A : Commutative-Ring l1)
  where

  integer-multiple-pred-Commutative-Ring :
    (k : ℤ) (x : type-Commutative-Ring A) →
    integer-multiple-Commutative-Ring A (pred-ℤ k) x ＝
    right-subtraction-Commutative-Ring A
      ( integer-multiple-Commutative-Ring A k x)
      ( x)
  integer-multiple-pred-Commutative-Ring =
    integer-multiple-pred-Ring (ring-Commutative-Ring A)

  integer-multiple-pred-Commutative-Ring' :
    (k : ℤ) (x : type-Commutative-Ring A) →
    integer-multiple-Commutative-Ring A (pred-ℤ k) x ＝
    left-subtraction-Commutative-Ring A
      ( x)
      ( integer-multiple-Commutative-Ring A k x)
  integer-multiple-pred-Commutative-Ring' =
    integer-multiple-pred-Ring' (ring-Commutative-Ring A)
```

### `k0 ＝ 0`

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  right-zero-law-integer-multiple-Commutative-Ring :
    (k : ℤ) →
    integer-multiple-Commutative-Ring A k (zero-Commutative-Ring A) ＝
    zero-Commutative-Ring A
  right-zero-law-integer-multiple-Commutative-Ring =
    left-zero-law-integer-multiple-Ring (ring-Commutative-Ring A)
```

### Integer multiples distribute over the sum of `x` and `y`

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  left-distributive-integer-multiple-add-Commutative-Ring :
    (k : ℤ) (x y : type-Commutative-Ring A) →
    integer-multiple-Commutative-Ring A k (add-Commutative-Ring A x y) ＝
    add-Commutative-Ring A
      ( integer-multiple-Commutative-Ring A k x)
      ( integer-multiple-Commutative-Ring A k y)
  left-distributive-integer-multiple-add-Commutative-Ring =
    left-distributive-integer-multiple-add-Ring (ring-Commutative-Ring A)
```

### Left and right integer multiple laws for ring multiplication

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  left-integer-multiple-law-mul-Commutative-Ring :
    (k : ℤ) (x y : type-Commutative-Ring A) →
    mul-Commutative-Ring A (integer-multiple-Commutative-Ring A k x) y ＝
    integer-multiple-Commutative-Ring A k (mul-Commutative-Ring A x y)
  left-integer-multiple-law-mul-Commutative-Ring =
    left-integer-multiple-law-mul-Ring (ring-Commutative-Ring A)

  right-integer-multiple-law-mul-Commutative-Ring :
    (k : ℤ) (x y : type-Commutative-Ring A) →
    mul-Commutative-Ring A x (integer-multiple-Commutative-Ring A k y) ＝
    integer-multiple-Commutative-Ring A k (mul-Commutative-Ring A x y)
  right-integer-multiple-law-mul-Commutative-Ring =
    right-integer-multiple-law-mul-Ring (ring-Commutative-Ring A)
```

### For each integer `k`, the operation of taking `k`-multiples is a group homomorphism

```agda
module _
  {l : Level} (A : Commutative-Ring l) (k : ℤ)
  where

  hom-ab-integer-multiple-Commutative-Ring :
    hom-Ab (ab-Commutative-Ring A) (ab-Commutative-Ring A)
  hom-ab-integer-multiple-Commutative-Ring =
    hom-ab-integer-multiple-Ring (ring-Commutative-Ring A) k
```

### Multiples by products of integers are iterated integer multiples

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  integer-multiple-mul-Commutative-Ring :
    (k l : ℤ) (x : type-Commutative-Ring A) →
    integer-multiple-Commutative-Ring A (k *ℤ l) x ＝
    integer-multiple-Commutative-Ring A k
      ( integer-multiple-Commutative-Ring A l x)
  integer-multiple-mul-Commutative-Ring =
    integer-multiple-mul-Ring (ring-Commutative-Ring A)
```

### Commutative ring homomorphisms preserve integer multiples

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (B : Commutative-Ring l2)
  (f : hom-Commutative-Ring A B)
  where

  preserves-integer-multiples-hom-Commutative-Ring :
    (k : ℤ) (x : type-Commutative-Ring A) →
    map-hom-Commutative-Ring A B f (integer-multiple-Commutative-Ring A k x) ＝
    integer-multiple-Commutative-Ring B k (map-hom-Commutative-Ring A B f x)
  preserves-integer-multiples-hom-Commutative-Ring =
    preserves-integer-multiples-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)

module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (B : Commutative-Ring l2)
  (f : hom-Commutative-Ring A B)
  where

  eq-integer-multiple-hom-Commutative-Ring :
    (g : hom-Commutative-Ring A B) (k : ℤ) (x : type-Commutative-Ring A) →
    ( map-hom-Commutative-Ring A B f x ＝ map-hom-Commutative-Ring A B g x) →
    map-hom-Commutative-Ring A B f (integer-multiple-Commutative-Ring A k x) ＝
    map-hom-Commutative-Ring A B g (integer-multiple-Commutative-Ring A k x)
  eq-integer-multiple-hom-Commutative-Ring g =
    eq-integer-multiple-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)
      ( g)
```
