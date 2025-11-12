# Integer multiples of elements of rings

```agda
module ring-theory.integer-multiples-of-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.homomorphisms-abelian-groups
open import group-theory.integer-multiples-of-elements-abelian-groups

open import ring-theory.commuting-elements-rings
open import ring-theory.homomorphisms-rings
open import ring-theory.multiples-of-elements-rings
open import ring-theory.rings
```

</details>

## Idea

The
{{#concept "integer multiple operation" Disambiguation="on a ring" Agda=integer-multiple-Ring}}
on a [ring](ring-theory.rings.md) is the map `k x ↦ kx`, which is defined by
[iteratively](foundation.iterating-automorphisms.md) adding `x` with itself an
[integer](elementary-number-theory.integers.md) `k` times.

## Definitions

### Iteratively adding `g`

```agda
module _
  {l : Level} (R : Ring l)
  where

  iterative-addition-by-element-Ring :
    type-Ring R → ℤ → type-Ring R → type-Ring R
  iterative-addition-by-element-Ring =
    iterative-addition-by-element-Ab (ab-Ring R)
```

### Integer multiples of elements of rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  integer-multiple-Ring : ℤ → type-Ring R → type-Ring R
  integer-multiple-Ring = integer-multiple-Ab (ab-Ring R)
```

### The predicate of being a natural multiple of an element in an ring

We say that an element `y` **is an integer multiple** of an element `x` if there
[exists](foundation.existential-quantification.md) an integer `k` such that
`kx ＝ y`.

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-integer-multiple-of-element-prop-Ring :
    (x y : type-Ring R) → Prop l
  is-integer-multiple-of-element-prop-Ring =
    is-integer-multiple-of-element-prop-Ab (ab-Ring R)

  is-integer-multiple-of-element-Ring :
    (x y : type-Ring R) → UU l
  is-integer-multiple-of-element-Ring =
    is-integer-multiple-of-element-Ab (ab-Ring R)

  is-prop-is-integer-multiple-of-element-Ring :
    (x y : type-Ring R) →
    is-prop (is-integer-multiple-of-element-Ring x y)
  is-prop-is-integer-multiple-of-element-Ring =
    is-prop-is-integer-multiple-of-element-Ab (ab-Ring R)
```

## Properties

### Associativity of iterated addition by a ring element

```agda
module _
  {l : Level} (R : Ring l) (a : type-Ring R)
  where

  associative-iterative-addition-by-element-Ring :
    (k : ℤ) (h1 h2 : type-Ring R) →
    iterative-addition-by-element-Ring R a k (add-Ring R h1 h2) ＝
    add-Ring R (iterative-addition-by-element-Ring R a k h1) h2
  associative-iterative-addition-by-element-Ring =
    associative-iterative-addition-by-element-Ab (ab-Ring R) a
```

### `integer-multiple-Ring R (int-ℕ n) a ＝ multiple-Ring R n a`

```agda
module _
  {l : Level} (R : Ring l)
  where

  integer-multiple-int-Ring :
    (n : ℕ) (a : type-Ring R) →
    integer-multiple-Ring R (int-ℕ n) a ＝ multiple-Ring R n a
  integer-multiple-int-Ring = integer-multiple-int-Ab (ab-Ring R)

  integer-multiple-in-pos-Ring :
    (n : ℕ) (a : type-Ring R) →
    integer-multiple-Ring R (in-pos-ℤ n) a ＝
    multiple-Ring R (succ-ℕ n) a
  integer-multiple-in-pos-Ring =
    integer-multiple-in-pos-Ab (ab-Ring R)

  integer-multiple-in-neg-Ring :
    (n : ℕ) (a : type-Ring R) →
    integer-multiple-Ring R (in-neg-ℤ n) a ＝
    neg-Ring R (multiple-Ring R (succ-ℕ n) a)
  integer-multiple-in-neg-Ring =
    integer-multiple-in-neg-Ab (ab-Ring R)
```

### The integer multiple `0x` is `0`

```agda
module _
  {l : Level} (R : Ring l) (a : type-Ring R)
  where

  integer-right-zero-law-multiple-Ring :
    integer-multiple-Ring R zero-ℤ a ＝ zero-Ring R
  integer-right-zero-law-multiple-Ring =
    integer-multiple-zero-Ab (ab-Ring R) a
```

### `1x ＝ x`

```agda
module _
  {l : Level} (R : Ring l) (a : type-Ring R)
  where

  integer-multiple-one-Ring :
    integer-multiple-Ring R one-ℤ a ＝ a
  integer-multiple-one-Ring =
    integer-multiple-one-Ab (ab-Ring R) a
```

### The integer multiple `(-1)x` is the negative of `x`

```agda
module _
  {l : Level} (R : Ring l) (a : type-Ring R)
  where

  integer-multiple-neg-one-Ring :
    integer-multiple-Ring R neg-one-ℤ a ＝ neg-Ring R a
  integer-multiple-neg-one-Ring =
    integer-multiple-neg-one-Ab (ab-Ring R) a
```

### The integer multiple `(x + y)a` computes to `xa + ya`

```agda
module _
  {l : Level} (R : Ring l) (a : type-Ring R)
  where

  distributive-integer-multiple-add-Ring :
    (x y : ℤ) →
    integer-multiple-Ring R (x +ℤ y) a ＝
    add-Ring R
      ( integer-multiple-Ring R x a)
      ( integer-multiple-Ring R y a)
  distributive-integer-multiple-add-Ring =
    distributive-integer-multiple-add-Ab (ab-Ring R) a
```

### The integer multiple `(-k)x` is the negative of the integer multiple `kx`

```agda
module _
  {l : Level} (R : Ring l)
  where

  integer-multiple-neg-Ring :
    (k : ℤ) (x : type-Ring R) →
    integer-multiple-Ring R (neg-ℤ k) x ＝
    neg-Ring R (integer-multiple-Ring R k x)
  integer-multiple-neg-Ring =
    integer-multiple-neg-Ab (ab-Ring R)
```

### `(k + 1)x = kx + x` and `(k + 1)x = x + kx`

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  integer-multiple-succ-Ring :
    (k : ℤ) (x : type-Ring R) →
    integer-multiple-Ring R (succ-ℤ k) x ＝
    add-Ring R (integer-multiple-Ring R k x) x
  integer-multiple-succ-Ring =
    integer-multiple-succ-Ab (ab-Ring R)

  integer-multiple-succ-Ring' :
    (k : ℤ) (x : type-Ring R) →
    integer-multiple-Ring R (succ-ℤ k) x ＝
    add-Ring R x (integer-multiple-Ring R k x)
  integer-multiple-succ-Ring' =
    integer-multiple-succ-Ab' (ab-Ring R)
```

### `(k - 1)x = kx - x` and `(k - 1)x = -x + kx`

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  integer-multiple-pred-Ring :
    (k : ℤ) (x : type-Ring R) →
    integer-multiple-Ring R (pred-ℤ k) x ＝
    right-subtraction-Ring R (integer-multiple-Ring R k x) x
  integer-multiple-pred-Ring =
    integer-multiple-pred-Ab (ab-Ring R)

  integer-multiple-pred-Ring' :
    (k : ℤ) (x : type-Ring R) →
    integer-multiple-Ring R (pred-ℤ k) x ＝
    left-subtraction-Ring R x (integer-multiple-Ring R k x)
  integer-multiple-pred-Ring' =
    integer-multiple-pred-Ab' (ab-Ring R)
```

### `k0 ＝ 0`

```agda
module _
  {l : Level} (R : Ring l)
  where

  right-zero-law-integer-multiple-Ring :
    (k : ℤ) → integer-multiple-Ring R k (zero-Ring R) ＝ zero-Ring R
  right-zero-law-integer-multiple-Ring =
    right-zero-law-integer-multiple-Ab (ab-Ring R)
```

### Integer multiples distribute over the sum of `x` and `y`

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-distributive-integer-multiple-add-Ring :
    (k : ℤ) (x y : type-Ring R) →
    integer-multiple-Ring R k (add-Ring R x y) ＝
    add-Ring R (integer-multiple-Ring R k x) (integer-multiple-Ring R k y)
  left-distributive-integer-multiple-add-Ring =
    left-distributive-integer-multiple-add-Ab (ab-Ring R)
```

### Left and right integer multiple laws for ring multiplication

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-integer-multiple-law-mul-Ring :
    (k : ℤ) (x y : type-Ring R) →
    mul-Ring R (integer-multiple-Ring R k x) y ＝
    integer-multiple-Ring R k (mul-Ring R x y)
  left-integer-multiple-law-mul-Ring (inl zero-ℕ) x y =
    ( ap (mul-Ring' R y) (integer-multiple-neg-one-Ring R x)) ∙
    ( ( left-negative-law-mul-Ring R x y) ∙
      ( inv (integer-multiple-neg-one-Ring R _)))
  left-integer-multiple-law-mul-Ring (inl (succ-ℕ k)) x y =
    ( ap (mul-Ring' R y) (integer-multiple-pred-Ring R (inl k) x)) ∙
    ( ( right-distributive-mul-right-subtraction-Ring R _ _ _) ∙
      ( ( ap
          ( λ u → right-subtraction-Ring R u _)
          ( left-integer-multiple-law-mul-Ring (inl k) _ _)) ∙
        ( inv (integer-multiple-pred-Ring R (inl k) _))))
  left-integer-multiple-law-mul-Ring (inr (inl _)) x y =
    ( ap (mul-Ring' R y) (integer-right-zero-law-multiple-Ring R x)) ∙
    ( left-zero-law-mul-Ring R y)
  left-integer-multiple-law-mul-Ring (inr (inr zero-ℕ)) x y =
    ( ap (mul-Ring' R y) (integer-multiple-one-Ring R x)) ∙
    ( inv (integer-multiple-one-Ring R _))
  left-integer-multiple-law-mul-Ring (inr (inr (succ-ℕ k))) x y =
    ( ap (mul-Ring' R y) (integer-multiple-succ-Ring R (inr (inr k)) x)) ∙
    ( ( right-distributive-mul-add-Ring R _ _ _) ∙
      ( ( ap
          ( add-Ring' R _)
          ( left-integer-multiple-law-mul-Ring (inr (inr k)) _ _)) ∙
        ( inv (integer-multiple-succ-Ring R (inr (inr k)) _))))

  right-integer-multiple-law-mul-Ring :
    (k : ℤ) (x y : type-Ring R) →
    mul-Ring R x (integer-multiple-Ring R k y) ＝
    integer-multiple-Ring R k (mul-Ring R x y)
  right-integer-multiple-law-mul-Ring (inl zero-ℕ) x y =
    ( ap (mul-Ring R x) (integer-multiple-neg-one-Ring R y)) ∙
    ( ( right-negative-law-mul-Ring R x y) ∙
      ( inv (integer-multiple-neg-one-Ring R _)))
  right-integer-multiple-law-mul-Ring (inl (succ-ℕ k)) x y =
    ( ap (mul-Ring R x) (integer-multiple-pred-Ring R (inl k) y)) ∙
    ( ( left-distributive-mul-right-subtraction-Ring R _ _ _) ∙
      ( ( ap
          ( add-Ring' R _)
          ( right-integer-multiple-law-mul-Ring (inl k) x y)) ∙
        ( inv (integer-multiple-pred-Ring R (inl k) _))))
  right-integer-multiple-law-mul-Ring (inr (inl _)) x y =
    ( ap (mul-Ring R x) (integer-right-zero-law-multiple-Ring R y)) ∙
    ( right-zero-law-mul-Ring R x)
  right-integer-multiple-law-mul-Ring (inr (inr zero-ℕ)) x y =
    ( ap (mul-Ring R x) (integer-multiple-one-Ring R y)) ∙
    ( inv (integer-multiple-one-Ring R _))
  right-integer-multiple-law-mul-Ring (inr (inr (succ-ℕ k))) x y =
    ( ap (mul-Ring R x) (integer-multiple-succ-Ring R (inr (inr k)) y)) ∙
    ( ( left-distributive-mul-add-Ring R x _ _) ∙
      ( ( ap
          ( add-Ring' R _)
          ( right-integer-multiple-law-mul-Ring (inr (inr k)) x y)) ∙
        ( inv (integer-multiple-succ-Ring R (inr (inr k)) _))))
```

### If `x` and `y` commute, then integer multiples of `x` and `y` commute

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-integer-multiple-Ring :
    (k : ℤ) {x y : type-Ring R} → commute-Ring R x y →
    commute-Ring R x (integer-multiple-Ring R k y)
  commute-integer-multiple-Ring (inl zero-ℕ) H =
    tr
      ( commute-Ring R _)
      ( inv (integer-multiple-neg-one-Ring R _))
      ( commute-neg-Ring R H)
  commute-integer-multiple-Ring (inl (succ-ℕ k)) H =
    tr
      ( commute-Ring R _)
      ( inv (integer-multiple-pred-Ring R (inl k) _))
      ( commute-right-subtraction-Ring R
        ( commute-integer-multiple-Ring (inl k) H)
        ( H))
  commute-integer-multiple-Ring (inr (inl _)) {x} H =
    tr
      ( commute-Ring R _)
      ( inv (integer-right-zero-law-multiple-Ring R x))
      ( inv (commute-zero-Ring R _))
  commute-integer-multiple-Ring (inr (inr zero-ℕ)) H =
    tr
      ( commute-Ring R _)
      ( inv (integer-multiple-one-Ring R _))
      ( H)
  commute-integer-multiple-Ring (inr (inr (succ-ℕ k))) H =
    tr
      ( commute-Ring R _)
      ( inv (integer-multiple-succ-Ring R (inr (inr k)) _))
      ( commute-add-Ring R
        ( commute-integer-multiple-Ring (inr (inr k)) H)
        ( H))

  commute-integer-multiples-Ring :
    (k l : ℤ) {x y : type-Ring R} → commute-Ring R x y →
    commute-Ring R (integer-multiple-Ring R k x) (integer-multiple-Ring R l y)
  commute-integer-multiples-Ring (inl zero-ℕ) l H =
    tr
      ( commute-Ring' R _)
      ( inv (integer-multiple-neg-one-Ring R _))
      ( inv (commute-neg-Ring R (inv (commute-integer-multiple-Ring l H))))
  commute-integer-multiples-Ring (inl (succ-ℕ k)) l H =
    tr
      ( commute-Ring' R _)
      ( inv (integer-multiple-pred-Ring R (inl k) _))
      ( inv
        ( commute-right-subtraction-Ring R
          ( commute-integer-multiples-Ring l (inl k) (inv H))
          ( inv (commute-integer-multiple-Ring l H))))
  commute-integer-multiples-Ring (inr (inl _)) l {x} H =
    tr
      ( commute-Ring' R _)
      ( inv (integer-right-zero-law-multiple-Ring R x))
      ( commute-zero-Ring R _)
  commute-integer-multiples-Ring (inr (inr zero-ℕ)) l H =
    tr
      ( commute-Ring' R _)
      ( inv (integer-multiple-one-Ring R _))
      ( commute-integer-multiple-Ring l H)
  commute-integer-multiples-Ring (inr (inr (succ-ℕ k))) l H =
    tr
      ( commute-Ring' R _)
      ( inv (integer-multiple-succ-Ring R (inr (inr k)) _))
      ( inv
        ( commute-add-Ring R
          ( commute-integer-multiples-Ring l (inr (inr k)) (inv H))
          ( inv (commute-integer-multiple-Ring l H))))

  commute-integer-multiples-diagonal-Ring :
    (k l : ℤ) {x : type-Ring R} →
    commute-Ring R (integer-multiple-Ring R k x) (integer-multiple-Ring R l x)
  commute-integer-multiples-diagonal-Ring k l =
    commute-integer-multiples-Ring k l refl
```

### For each integer `k`, the operation of taking `k`-multiples is a group homomorphism

```agda
module _
  {l : Level} (R : Ring l) (k : ℤ)
  where

  hom-ab-integer-multiple-Ring : hom-Ab (ab-Ring R) (ab-Ring R)
  hom-ab-integer-multiple-Ring = hom-integer-multiple-Ab (ab-Ring R) k
```

### Multiples by products of integers are iterated integer multiples

```agda
module _
  {l : Level} (R : Ring l)
  where

  integer-multiple-mul-Ring :
    (k l : ℤ) (x : type-Ring R) →
    integer-multiple-Ring R (k *ℤ l) x ＝
    integer-multiple-Ring R k (integer-multiple-Ring R l x)
  integer-multiple-mul-Ring =
    integer-multiple-mul-Ab (ab-Ring R)

  swap-integer-multiple-Ring :
    (k l : ℤ) (x : type-Ring R) →
    integer-multiple-Ring R k (integer-multiple-Ring R l x) ＝
    integer-multiple-Ring R l (integer-multiple-Ring R k x)
  swap-integer-multiple-Ring =
    swap-integer-multiple-Ab (ab-Ring R)
```

### Ring homomorphisms preserve integer multiples

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (f : hom-Ring R S)
  where

  preserves-integer-multiples-hom-Ring :
    (k : ℤ) (x : type-Ring R) →
    map-hom-Ring R S f (integer-multiple-Ring R k x) ＝
    integer-multiple-Ring S k (map-hom-Ring R S f x)
  preserves-integer-multiples-hom-Ring =
    preserves-integer-multiples-hom-Ab
      ( ab-Ring R)
      ( ab-Ring S)
      ( hom-ab-hom-Ring R S f)

module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (f : hom-Ring R S)
  where

  eq-integer-multiple-hom-Ring :
    (g : hom-Ring R S) (k : ℤ) (x : type-Ring R) →
    ( map-hom-Ring R S f x ＝ map-hom-Ring R S g x) →
    map-hom-Ring R S f (integer-multiple-Ring R k x) ＝
    map-hom-Ring R S g (integer-multiple-Ring R k x)
  eq-integer-multiple-hom-Ring g =
    eq-integer-multiple-hom-Ab
      ( ab-Ring R)
      ( ab-Ring S)
      ( hom-ab-hom-Ring R S f)
      ( hom-ab-hom-Ring R S g)
```

### Ring homomorphisms preserve integer multiples of `1`

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (f : hom-Ring R S)
  where

  preserves-integer-multiple-one-hom-Ring :
    (k : ℤ) →
    map-hom-Ring R S f (integer-multiple-Ring R k (one-Ring R)) ＝
    integer-multiple-Ring S k (one-Ring S)
  preserves-integer-multiple-one-hom-Ring k =
    ( preserves-integer-multiples-hom-Ring R S f k (one-Ring R)) ∙
    ( ap (integer-multiple-Ring S k) (preserves-one-hom-Ring R S f))
```
