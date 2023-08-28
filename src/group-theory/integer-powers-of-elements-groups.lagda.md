# Integer powers of elements of groups

```agda
module group-theory.integer-powers-of-elements-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.identity-types
open import foundation.iterating-automorphisms
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.commuting-elements-groups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.powers-of-elements-groups

open import structured-types.initial-pointed-type-equipped-with-automorphism
```

</details>

## Idea

The **integer power operation** on a [group](group-theory.groups.md) is the map `k x ↦ xᵏ`, which is defined by
[iteratively](foundation.iterating-automorphisms.md) the automorphism multiplying `x` with itself an [integer](elementary-number-theory.integers.md) `k` times.

## Definitions

### Iterating multiplication by `g`

```agda
module _
  {l : Level} (G : Group l)
  where

  iterated-multiplication-by-element-Group :
    type-Group G → ℤ → type-Group G → type-Group G
  iterated-multiplication-by-element-Group g k =
    map-iterate-automorphism-ℤ k (equiv-mul-Group G g)
```

### Powers by integers of group elements

```agda
module _
  {l : Level} (G : Group l)
  where

  integer-power-Group : ℤ → type-Group G → type-Group G
  integer-power-Group k g =
    map-iterate-automorphism-ℤ k (equiv-mul-Group G g) (unit-Group G)
```

## Properties

### Associativity of iterated multiplication by a group element

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  associative-iterated-multiplication-by-element-Group :
    (k : ℤ) (h1 h2 : type-Group G) →
    iterated-multiplication-by-element-Group G g k (mul-Group G h1 h2) ＝
    mul-Group G (iterated-multiplication-by-element-Group G g k h1) h2
  associative-iterated-multiplication-by-element-Group
    ( inl zero-ℕ) h1 h2 =
    inv (associative-mul-Group G (inv-Group G g) h1 h2)
  associative-iterated-multiplication-by-element-Group
    ( inl (succ-ℕ x)) h1 h2 =
    ( ap
      ( mul-Group G (inv-Group G g))
      ( associative-iterated-multiplication-by-element-Group
        ( inl x)
        ( h1)
        ( h2))) ∙
    ( inv
      ( associative-mul-Group G
        ( inv-Group G g)
        ( iterated-multiplication-by-element-Group G g (inl x) h1)
        ( h2)))
  associative-iterated-multiplication-by-element-Group
    ( inr (inl star)) h1 h2 =
    refl
  associative-iterated-multiplication-by-element-Group
    ( inr (inr zero-ℕ)) h1 h2 =
    inv (associative-mul-Group G g h1 h2)
  associative-iterated-multiplication-by-element-Group
    ( inr (inr (succ-ℕ x))) h1 h2 =
    ( ap
      ( mul-Group G g)
      ( associative-iterated-multiplication-by-element-Group
        ( inr (inr x))
        ( h1)
        ( h2))) ∙
    ( inv
      ( associative-mul-Group G g
        ( iterated-multiplication-by-element-Group G g (inr (inr x)) h1)
        ( h2)))
```

### `integer-power-Group G (int-ℕ n) g ＝ power-Group G n g`

```agda
module _
  {l : Level} (G : Group l)
  where

  integer-power-int-Group :
    (n : ℕ) (g : type-Group G) →
    integer-power-Group G (int-ℕ n) g ＝ power-Group G n g
  integer-power-int-Group zero-ℕ g = refl
  integer-power-int-Group (succ-ℕ zero-ℕ) g = right-unit-law-mul-Group G g
  integer-power-int-Group (succ-ℕ (succ-ℕ n)) g =
    ( ap (mul-Group G g) (integer-power-int-Group (succ-ℕ n) g)) ∙
    ( inv (power-succ-Group' G (succ-ℕ n) g))

  integer-power-in-pos-Group :
    (n : ℕ) (g : type-Group G) →
    integer-power-Group G (in-pos n) g ＝
    power-Group G (succ-ℕ n) g
  integer-power-in-pos-Group n g = integer-power-int-Group (succ-ℕ n) g

  integer-power-in-neg-Group :
    (n : ℕ) (g : type-Group G) →
    integer-power-Group G (in-neg n) g ＝
    inv-Group G (power-Group G (succ-ℕ n) g)
  integer-power-in-neg-Group zero-ℕ g =
    right-unit-law-mul-Group G (inv-Group G g)
  integer-power-in-neg-Group (succ-ℕ n) g =
    ( ap (mul-Group G (inv-Group G g)) (integer-power-in-neg-Group n g)) ∙
    ( ( inv (distributive-inv-mul-Group G (power-Group G (succ-ℕ n) g) g)) ∙
      ( ap (inv-Group G) (power-succ-Group G (succ-ℕ n) g)))
```

### The integer power `x⁰` is the unit of the group

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  integer-power-zero-Group :
    integer-power-Group G zero-ℤ g ＝ unit-Group G
  integer-power-zero-Group =
    preserves-point-map-ℤ-Pointed-Type-With-Aut
      ( pointed-type-with-aut-Group G g)
```

### `x¹ ＝ x`

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  integer-power-one-Group :
    integer-power-Group G one-ℤ g ＝ g
  integer-power-one-Group = right-unit-law-mul-Group G g
```

### The integer power `x⁻¹` is the inverse of `x`

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  integer-power-neg-one-Group :
    integer-power-Group G neg-one-ℤ g ＝ inv-Group G g
  integer-power-neg-one-Group = right-unit-law-mul-Group G (inv-Group G g)
```

### The integer power `gˣ⁺ʸ` computes to `gˣgʸ`

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  distributive-integer-power-add-Group :
    (x y : ℤ) →
    ( integer-power-Group G (x +ℤ y) g) ＝
    ( mul-Group G
      ( integer-power-Group G x g)
      ( integer-power-Group G y g))
  distributive-integer-power-add-Group x y =
    ( iterate-automorphism-add-ℤ x y (equiv-mul-Group G g) (unit-Group G)) ∙
    ( ( ap
        ( iterated-multiplication-by-element-Group G g x)
        ( inv (left-unit-law-mul-Group G
          ( integer-power-Group G y g)))) ∙
      ( associative-iterated-multiplication-by-element-Group G g x
        ( unit-Group G)
        ( integer-power-Group G y g)))
```

### The integer power `x⁻ᵏ` is the inverse of the integer power `xᵏ`

```agda
module _
  {l : Level} (G : Group l)
  where

  integer-power-neg-Group :
    (k : ℤ) (x : type-Group G) →
    integer-power-Group G (neg-ℤ k) x ＝ inv-Group G (integer-power-Group G k x)
  integer-power-neg-Group (inl k) x =
    transpose-eq-inv-Group G
      ( ( ap (inv-Group G) (integer-power-in-pos-Group G k x)) ∙
        ( inv (integer-power-in-neg-Group G k x)))
  integer-power-neg-Group (inr (inl star)) x =
    ( integer-power-zero-Group G x) ∙
    ( inv (inv-unit-Group G))
  integer-power-neg-Group (inr (inr k)) x =
    ( integer-power-in-neg-Group G k x) ∙
    ( ap (inv-Group G) (inv (integer-power-in-pos-Group G k x)))
```

### `xᵏ⁺¹ = xᵏx`

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  integer-power-succ-Group :
    (k : ℤ) (x : type-Group G) →
    integer-power-Group G (succ-ℤ k) x ＝
    mul-Group G (integer-power-Group G k x) x
  integer-power-succ-Group k x =
    ( ap (λ t → integer-power-Group G t x) (is-right-add-one-succ-ℤ k)) ∙
    ( ( distributive-integer-power-add-Group G x k one-ℤ) ∙
      ( ap (mul-Group G _) (integer-power-one-Group G x)))
```

### `xᵏ⁺¹ = xxᵏ`

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  integer-power-succ-Group' :
    (k : ℤ) (x : type-Group G) →
    integer-power-Group G (succ-ℤ k) x ＝
    mul-Group G x (integer-power-Group G k x)
  integer-power-succ-Group' k x =
    ( ap (λ t → integer-power-Group G t x) (is-left-add-one-succ-ℤ k)) ∙
    ( ( distributive-integer-power-add-Group G x one-ℤ k) ∙
      ( ap (mul-Group' G _) (integer-power-one-Group G x)))
```

### `1ᵏ ＝ 1`

```agda
module _
  {l : Level} (G : Group l)
  where

  integer-power-unit-Group :
    (k : ℤ) → integer-power-Group G k (unit-Group G) ＝ unit-Group G
  integer-power-unit-Group (inl zero-ℕ) =
    integer-power-neg-one-Group G (unit-Group G) ∙ inv-unit-Group G
  integer-power-unit-Group (inl (succ-ℕ k)) =
    ( ap-mul-Group G (inv-unit-Group G) (integer-power-unit-Group (inl k))) ∙
    ( left-unit-law-mul-Group G (unit-Group G))
  integer-power-unit-Group (inr (inl star)) = refl
  integer-power-unit-Group (inr (inr zero-ℕ)) =
    integer-power-one-Group G (unit-Group G)
  integer-power-unit-Group (inr (inr (succ-ℕ k))) =
    left-unit-law-mul-Group G _ ∙ integer-power-unit-Group (inr (inr k))
```

### If `x` commutes with `y` then so do their integer powers

```agda
module _
  {l : Level} (G : Group l)
  where

  private
  
    infixl 50 _*_
    _*_ = mul-Group G

    pwr = integer-power-Group G
    
    infixr 60 _^_
    _^_ : (x : type-Group G) (k : ℤ) → type-Group G
    _^_ x k = integer-power-Group G k x

    infix 70 _⁻¹
    _⁻¹ = inv-Group G

  commute-integer-powers-Group' :
    (k : ℤ) {x y : type-Group G} →
    commute-Group G x y → commute-Group G x (y ^ k)
  commute-integer-powers-Group' (inl zero-ℕ) {x} {y} H =
    ( ap (x *_) (integer-power-neg-one-Group G y)) ∙
    ( ( commute-inv-Group G x y H) ∙
      ( ap (_* x) (inv (integer-power-neg-one-Group G y))))
  commute-integer-powers-Group' (inl (succ-ℕ k)) {x} {y} H =
    commute-mul-Group G x
      ( inv-Group G y)
      ( integer-power-Group G (inl k) y)
      ( commute-inv-Group G x y H)
      ( commute-integer-powers-Group' (inl k) H)
  commute-integer-powers-Group' (inr (inl star)) {x} {y} H =
    commute-unit-Group G x
  commute-integer-powers-Group' (inr (inr zero-ℕ)) {x} {y} H =
    ( ap (x *_) (integer-power-one-Group G y)) ∙
    ( ( H) ∙
      ( ap (_* x) (inv (integer-power-one-Group G y))))
  commute-integer-powers-Group' (inr (inr (succ-ℕ k))) {x} {y} H =
    commute-mul-Group G x y
      ( integer-power-Group G (inr (inr k)) y)
      ( H)
      ( commute-integer-powers-Group' (inr (inr k)) H)

  commute-integer-powers-Group :
    (k l : ℤ) {x y : type-Group G} →
    commute-Group G x y → commute-Group G (x ^ k) (y ^ l)
  commute-integer-powers-Group (inl zero-ℕ) l {x} {y} H =
    ( ap (_* y ^ l) (integer-power-neg-one-Group G x)) ∙
    ( ( inv
        ( commute-inv-Group G
          ( y ^ l)
          ( x)
          ( inv (commute-integer-powers-Group' l H)))) ∙
      ( ap (y ^ l *_) (inv (integer-power-neg-one-Group G x))))
  commute-integer-powers-Group (inl (succ-ℕ k)) l {x} {y} H =
    inv
      ( commute-mul-Group G
        ( y ^ l)
        ( inv-Group G x)
        ( x ^ inl k)
        ( commute-inv-Group G (y ^ l) x
          ( inv (commute-integer-powers-Group' l H)))
        ( inv (commute-integer-powers-Group (inl k) l H)))
  commute-integer-powers-Group (inr (inl star)) l {x} {y} H =
    inv (commute-unit-Group G (y ^ l))
  commute-integer-powers-Group (inr (inr zero-ℕ)) l {x} {y} H =
    ( ap (_* y ^ l) (integer-power-one-Group G x)) ∙
    ( ( commute-integer-powers-Group' l H) ∙
      ( ap (y ^ l *_) (inv (integer-power-one-Group G x))))
  commute-integer-powers-Group (inr (inr (succ-ℕ k))) l {x} {y} H =
    inv
      ( commute-mul-Group G
        ( y ^ l)
        ( x)
        ( x ^ inr (inr k))
        ( inv (commute-integer-powers-Group' l H))
        ( inv (commute-integer-powers-Group (inr (inr k)) l H)))
```

### If `x` commutes with `y`, then integer powers distribute over the product of `x` and `y`

### Powers by products of natural numbers are iterated powers

### Group homomorphisms preserve integer powers

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : type-hom-Group G H)
  where
  
  preserves-integer-powers-hom-Group :
    (k : ℤ) (x : type-Group G) →
    map-hom-Group G H f (integer-power-Group G k x) ＝
    integer-power-Group H k (map-hom-Group G H f x)
  preserves-integer-powers-hom-Group (inl zero-ℕ) x =
    ( preserves-mul-hom-Group G H f (inv-Group G x) (unit-Group G)) ∙
    ( ap-mul-Group H
      ( preserves-inv-hom-Group G H f x)
      ( preserves-unit-hom-Group G H f))
  preserves-integer-powers-hom-Group (inl (succ-ℕ k)) x =
    ( preserves-mul-hom-Group G H f
      ( inv-Group G x)
      ( integer-power-Group G (inl k) x)) ∙
    ( ap-mul-Group H
      ( preserves-inv-hom-Group G H f x)
      ( preserves-integer-powers-hom-Group (inl k) x))
  preserves-integer-powers-hom-Group (inr (inl star)) x =
    preserves-unit-hom-Group G H f
  preserves-integer-powers-hom-Group (inr (inr zero-ℕ)) x =
    ( preserves-mul-hom-Group G H f x (unit-Group G)) ∙
    ( ap (mul-Group H (map-hom-Group G H f x)) (preserves-unit-hom-Group G H f))
  preserves-integer-powers-hom-Group (inr (inr (succ-ℕ k))) x =
    ( preserves-mul-hom-Group G H f x (integer-power-Group G (inr (inr k)) x)) ∙
    ( ap
      ( mul-Group H (map-hom-Group G H f x))
      ( preserves-integer-powers-hom-Group (inr (inr k)) x))

module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : type-hom-Group G H)
  where

  eq-integer-power-hom-Group :
    (g : type-hom-Group G H) (k : ℤ) (x : type-Group G) →
    ( map-hom-Group G H f x ＝ map-hom-Group G H g x) →
    ( map-hom-Group G H f (integer-power-Group G k x) ＝
      map-hom-Group G H g (integer-power-Group G k x))
  eq-integer-power-hom-Group g k x p =
    ( preserves-integer-powers-hom-Group G H f k x) ∙
    ( ( ap (integer-power-Group H k) p) ∙
      ( inv (preserves-integer-powers-hom-Group G H g k x)))
```
