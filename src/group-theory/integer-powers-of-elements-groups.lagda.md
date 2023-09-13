# Integer powers of elements of groups

```agda
module group-theory.integer-powers-of-elements-groups where
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
open import foundation.iterating-automorphisms
open import foundation.universe-levels

open import group-theory.commuting-elements-groups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.powers-of-elements-groups

open import structured-types.initial-pointed-type-equipped-with-automorphism
```

</details>

## Idea

The **integer power operation** on a [group](group-theory.groups.md) is the map
`k x ↦ xᵏ`, which is defined by
[iteratively](foundation.iterating-automorphisms.md) multiplying `x` with itself
an [integer](elementary-number-theory.integers.md) `k` times.

## Definitions

### Iteratively multiplication by `g`

```agda
module _
  {l : Level} (G : Group l)
  where

  iterative-multiplication-by-element-Group :
    type-Group G → ℤ → type-Group G → type-Group G
  iterative-multiplication-by-element-Group g k =
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

  associative-iterative-multiplication-by-element-Group :
    (k : ℤ) (h1 h2 : type-Group G) →
    iterative-multiplication-by-element-Group G g k (mul-Group G h1 h2) ＝
    mul-Group G (iterative-multiplication-by-element-Group G g k h1) h2
  associative-iterative-multiplication-by-element-Group
    ( inl zero-ℕ) h1 h2 =
    inv (associative-mul-Group G (inv-Group G g) h1 h2)
  associative-iterative-multiplication-by-element-Group
    ( inl (succ-ℕ x)) h1 h2 =
    ( ap
      ( mul-Group G (inv-Group G g))
      ( associative-iterative-multiplication-by-element-Group
        ( inl x)
        ( h1)
        ( h2))) ∙
    ( inv
      ( associative-mul-Group G
        ( inv-Group G g)
        ( iterative-multiplication-by-element-Group G g (inl x) h1)
        ( h2)))
  associative-iterative-multiplication-by-element-Group
    ( inr (inl star)) h1 h2 =
    refl
  associative-iterative-multiplication-by-element-Group
    ( inr (inr zero-ℕ)) h1 h2 =
    inv (associative-mul-Group G g h1 h2)
  associative-iterative-multiplication-by-element-Group
    ( inr (inr (succ-ℕ x))) h1 h2 =
    ( ap
      ( mul-Group G g)
      ( associative-iterative-multiplication-by-element-Group
        ( inr (inr x))
        ( h1)
        ( h2))) ∙
    ( inv
      ( associative-mul-Group G g
        ( iterative-multiplication-by-element-Group G g (inr (inr x)) h1)
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
    ( inv (distributive-inv-mul-Group G (power-Group G (succ-ℕ n) g) g)) ∙
    ( ap (inv-Group G) (power-succ-Group G (succ-ℕ n) g))
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
    integer-power-Group G (x +ℤ y) g ＝
    mul-Group G
      ( integer-power-Group G x g)
      ( integer-power-Group G y g)
  distributive-integer-power-add-Group x y =
    ( iterate-automorphism-add-ℤ x y (equiv-mul-Group G g) (unit-Group G)) ∙
    ( ap
      ( iterative-multiplication-by-element-Group G g x)
      ( inv (left-unit-law-mul-Group G (integer-power-Group G y g)))) ∙
    ( associative-iterative-multiplication-by-element-Group G g x
      ( unit-Group G)
      ( integer-power-Group G y g))
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
    integer-power-zero-Group G x ∙ inv (inv-unit-Group G)
  integer-power-neg-Group (inr (inr k)) x =
    ( integer-power-in-neg-Group G k x) ∙
    ( ap (inv-Group G) (inv (integer-power-in-pos-Group G k x)))
```

### `xᵏ⁺¹ = xᵏx` and `xᵏ⁺¹ = xxᵏ`

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
    ( distributive-integer-power-add-Group G x k one-ℤ) ∙
    ( ap (mul-Group G _) (integer-power-one-Group G x))

  integer-power-succ-Group' :
    (k : ℤ) (x : type-Group G) →
    integer-power-Group G (succ-ℤ k) x ＝
    mul-Group G x (integer-power-Group G k x)
  integer-power-succ-Group' k x =
    ( ap (λ t → integer-power-Group G t x) (is-left-add-one-succ-ℤ k)) ∙
    ( distributive-integer-power-add-Group G x one-ℤ k) ∙
    ( ap (mul-Group' G _) (integer-power-one-Group G x))
```

### `xᵏ⁻¹ = xᵏx⁻¹` and `xᵏ⁻¹ = x⁻¹xᵏ`

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  private

    infixl 45 _*_
    _*_ = mul-Group G

    pwr = integer-power-Group G

    infixr 50 _^_
    _^_ : (x : type-Group G) (k : ℤ) → type-Group G
    _^_ x k = integer-power-Group G k x

    infix 55 _⁻¹
    _⁻¹ = inv-Group G

  integer-power-pred-Group :
    (k : ℤ) (x : type-Group G) → x ^ (pred-ℤ k) ＝ x ^ k * x ⁻¹
  integer-power-pred-Group k x =
    ( ap (x ^_) (is-right-add-neg-one-pred-ℤ k)) ∙
    ( distributive-integer-power-add-Group G x k neg-one-ℤ) ∙
    ( ap ((x ^ k) *_) (integer-power-neg-one-Group G x))

  integer-power-pred-Group' :
    (k : ℤ) (x : type-Group G) → x ^ (pred-ℤ k) ＝ x ⁻¹ * x ^ k
  integer-power-pred-Group' k x =
    ( ap (x ^_) (is-left-add-neg-one-pred-ℤ k)) ∙
    ( distributive-integer-power-add-Group G x neg-one-ℤ k) ∙
    ( ap (_* (x ^ k)) (integer-power-neg-one-Group G x))
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

    infixl 45 _*_
    _*_ = mul-Group G

    pwr = integer-power-Group G

    infixr 50 _^_
    _^_ : (x : type-Group G) (k : ℤ) → type-Group G
    _^_ x k = integer-power-Group G k x

    infix 55 _⁻¹
    _⁻¹ = inv-Group G

  commute-integer-powers-Group' :
    (k : ℤ) {x y : type-Group G} →
    commute-Group G x y → commute-Group G x (y ^ k)
  commute-integer-powers-Group' (inl zero-ℕ) {x} {y} H =
    ( ap (x *_) (integer-power-neg-one-Group G y)) ∙
    ( commute-inv-Group G x y H) ∙
    ( ap (_* x) (inv (integer-power-neg-one-Group G y)))
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
    ( H) ∙
    ( ap (_* x) (inv (integer-power-one-Group G y)))
  commute-integer-powers-Group' (inr (inr (succ-ℕ k))) {x} {y} H =
    commute-mul-Group G x y
      ( integer-power-Group G (inr (inr k)) y)
      ( H)
      ( commute-integer-powers-Group' (inr (inr k)) H)

  commute-integer-powers-Group :
    (k l : ℤ) {x y : type-Group G} →
    commute-Group G x y → commute-Group G (x ^ k) (y ^ l)
  commute-integer-powers-Group (inl zero-ℕ) l {x} {y} H =
    ( ap (_* (y ^ l)) (integer-power-neg-one-Group G x)) ∙
    ( inv
      ( commute-inv-Group G
        ( y ^ l)
        ( x)
        ( inv (commute-integer-powers-Group' l H)))) ∙
    ( ap ((y ^ l) *_) (inv (integer-power-neg-one-Group G x)))
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
    ( ap (_* (y ^ l)) (integer-power-one-Group G x)) ∙
    ( commute-integer-powers-Group' l H) ∙
    ( ap ((y ^ l) *_) (inv (integer-power-one-Group G x)))
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

```agda
module _
  {l : Level} (G : Group l)
  where

  private

    infixl 45 _*_
    _*_ = mul-Group G

    pwr = integer-power-Group G

    infixr 50 _^_
    _^_ : (x : type-Group G) (k : ℤ) → type-Group G
    _^_ x k = integer-power-Group G k x

    infix 55 _⁻¹
    _⁻¹ = inv-Group G

  distributive-integer-power-mul-Group :
    (k : ℤ) (x y : type-Group G) →
    commute-Group G x y → (x * y) ^ k ＝ x ^ k * y ^ k
  distributive-integer-power-mul-Group (inl zero-ℕ) x y H =
    equational-reasoning
      (x * y) ^ neg-one-ℤ
      ＝ (x * y) ⁻¹
        by integer-power-neg-one-Group G (x * y)
      ＝ x ⁻¹ * y ⁻¹
        by distributive-inv-mul-Group' G x y H
      ＝ x ^ neg-one-ℤ * y ^ neg-one-ℤ
        by
        inv
          ( ap-mul-Group G
            ( integer-power-neg-one-Group G x)
            ( integer-power-neg-one-Group G y))
  distributive-integer-power-mul-Group (inl (succ-ℕ k)) x y H =
    equational-reasoning
      (x * y) ^ (pred-ℤ (inl k))
      ＝ (x * y) ^ (inl k) * (x * y) ⁻¹
        by integer-power-pred-Group G (inl k) (x * y)
      ＝ (x ^ (inl k) * y ^ (inl k)) * (x ⁻¹ * y ⁻¹)
        by
        ap-mul-Group G
          ( distributive-integer-power-mul-Group (inl k) x y H)
          ( distributive-inv-mul-Group' G x y H)
      ＝ (x ^ (inl k) * x ⁻¹) * (y ^ (inl k) * y ⁻¹)
        by
        interchange-mul-mul-Group G
          ( double-transpose-eq-mul-Group' G
            ( commute-integer-powers-Group' G (inl k) H))
      ＝ (x ^ (pred-ℤ (inl k))) * (y ^ (pred-ℤ (inl k)))
        by
        ap-mul-Group G
          ( inv (integer-power-pred-Group G (inl k) x))
          ( inv (integer-power-pred-Group G (inl k) y))
  distributive-integer-power-mul-Group (inr (inl star)) x y H =
    inv (left-unit-law-mul-Group G (unit-Group G))
  distributive-integer-power-mul-Group (inr (inr zero-ℕ)) x y H =
    ( integer-power-one-Group G (x * y)) ∙
    ( inv
      ( ap-mul-Group G
        ( integer-power-one-Group G x)
        ( integer-power-one-Group G y)))
  distributive-integer-power-mul-Group (inr (inr (succ-ℕ k))) x y H =
    equational-reasoning
      (x * y) ^ (succ-ℤ (in-pos k))
      ＝ (x * y) ^ (in-pos k) * (x * y)
        by integer-power-succ-Group G (in-pos k) (x * y)
      ＝ (x ^ (in-pos k) * y ^ (in-pos k)) * (x * y)
        by
        ap
          ( _* (x * y))
          ( distributive-integer-power-mul-Group (inr (inr k)) x y H)
      ＝ (x ^ (in-pos k) * x) * (y ^ (in-pos k) * y)
        by
        interchange-mul-mul-Group G
          ( inv (commute-integer-powers-Group' G (in-pos k) H))
      ＝ x ^ (succ-ℤ (in-pos k)) * y ^ (succ-ℤ (in-pos k))
        by
        ap-mul-Group G
          ( inv (integer-power-succ-Group G (in-pos k) x))
          ( inv (integer-power-succ-Group G (in-pos k) y))
```

### Powers by products of integers are iterated integer powers

```agda
module _
  {l : Level} (G : Group l)
  where

  private

    infixl 45 _*_
    _*_ = mul-ℤ

    pwr = integer-power-Group G

    infixr 50 _^_
    _^_ : (x : type-Group G) (k : ℤ) → type-Group G
    _^_ x k = integer-power-Group G k x

  integer-power-mul-Group :
    (k l : ℤ) (x : type-Group G) → x ^ (k * l) ＝ (x ^ k) ^ l
  integer-power-mul-Group k (inl zero-ℕ) x =
    ( ap (x ^_) (right-neg-unit-law-mul-ℤ k)) ∙
    ( integer-power-neg-Group G k x) ∙
    ( inv (integer-power-neg-one-Group G _))
  integer-power-mul-Group k (inl (succ-ℕ l)) x =
    equational-reasoning
      (x ^ (k * inl (succ-ℕ l)))
      ＝ x ^ (neg-ℤ k +ℤ (k *ℤ inl l))
        by ap (x ^_) (right-predecessor-law-mul-ℤ k (inl l))
      ＝ mul-Group G (x ^ neg-ℤ k) (x ^ (k * (inl l)))
        by distributive-integer-power-add-Group G x (neg-ℤ k) _
      ＝ mul-Group G ((x ^ k) ^ neg-one-ℤ) ((x ^ k) ^ (inl l))
        by
        ap-mul-Group G
          ( ( integer-power-neg-Group G k x) ∙
            ( inv (integer-power-neg-one-Group G (x ^ k))))
          ( integer-power-mul-Group k (inl l) x)
      ＝ (x ^ k) ^ (neg-one-ℤ +ℤ (inl l))
        by
        inv (distributive-integer-power-add-Group G (x ^ k) neg-one-ℤ (inl l))
      ＝ (x ^ k) ^ (inl (succ-ℕ l))
        by ap ((x ^ k) ^_) (is-left-add-neg-one-pred-ℤ (inl l))
  integer-power-mul-Group k (inr (inl star)) x =
    ap (x ^_) (right-zero-law-mul-ℤ k)
  integer-power-mul-Group k (inr (inr zero-ℕ)) x =
    ( ap (x ^_) (right-unit-law-mul-ℤ k)) ∙
    ( inv (integer-power-one-Group G _))
  integer-power-mul-Group k (inr (inr (succ-ℕ l))) x =
    equational-reasoning
      (x ^ (k * succ-ℤ (in-pos l)))
      ＝ x ^ (k +ℤ k * (in-pos l))
        by ap (x ^_) (right-successor-law-mul-ℤ k (in-pos l))
      ＝ mul-Group G (x ^ k) (x ^ (k * in-pos l))
        by
        distributive-integer-power-add-Group G x k (k * in-pos l)
      ＝ mul-Group G (x ^ k) ((x ^ k) ^ (in-pos l))
        by
        ap (mul-Group G _) (integer-power-mul-Group k (inr (inr l)) x)
      ＝ (x ^ k) ^ (succ-ℤ (in-pos l))
        by
        inv (integer-power-succ-Group' G (in-pos l) (x ^ k))
```

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
    ( ap (integer-power-Group H k) p) ∙
    ( inv (preserves-integer-powers-hom-Group G H g k x))
```
