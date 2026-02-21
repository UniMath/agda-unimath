# Integer powers of elements in large groups

```agda
module group-theory.integer-powers-of-elements-large-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.integer-powers-of-elements-groups
open import group-theory.large-groups
open import group-theory.powers-of-elements-large-groups
open import group-theory.powers-of-elements-large-monoids
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="raising an element of a large group to an integer power" Agda=int-power-Large-Group}}
on a [large group](group-theory.large-groups.md) is the map `n x ↦ xⁿ`, which is
defined by [iteratively](foundation.iterating-functions.md) multiplying `x` with
itself `n` times. In this file we consider the case where `n` is an
[integer](elementary-number-theory.integers.md).

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  int-power-Large-Group :
    {l : Level} → ℤ → type-Large-Group G l → type-Large-Group G l
  int-power-Large-Group {l} = integer-power-Group (group-Large-Group G l)
```

## Properties

### The standard embedding of natural numbers in the integers preserves powers of large group elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    int-power-int-Large-Group :
      {l : Level} (n : ℕ) (x : type-Large-Group G l) →
      int-power-Large-Group G (int-ℕ n) x ＝ power-Large-Group G n x
    int-power-int-Large-Group {l} =
      integer-power-int-Group (group-Large-Group G l)
```

### The integer power `x⁰` is the unit element

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    int-power-zero-Large-Group :
      {l : Level} (x : type-Large-Group G l) →
      int-power-Large-Group G zero-ℤ x ＝ raise-unit-Large-Group G l
    int-power-zero-Large-Group {l} =
      integer-power-zero-Group (group-Large-Group G l)
```

### `x¹ ＝ x`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    int-power-one-Large-Group :
      {l : Level} (x : type-Large-Group G l) →
      int-power-Large-Group G one-ℤ x ＝ x
    int-power-one-Large-Group {l} =
      integer-power-one-Group (group-Large-Group G l)
```

### The integer power `x⁻¹` is the inverse of `x`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    int-power-neg-one-Large-Group :
      {l : Level} (x : type-Large-Group G l) →
      int-power-Large-Group G neg-one-ℤ x ＝ inv-Large-Group G x
    int-power-neg-one-Large-Group {l} =
      integer-power-neg-one-Group (group-Large-Group G l)
```

### The integer power `xᵐ⁺ⁿ` computes to `xᵐxⁿ`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    distributive-int-power-add-Large-Group :
      {l : Level} (x : type-Large-Group G l) (m n : ℤ) →
      int-power-Large-Group G (m +ℤ n) x ＝
      mul-Large-Group G
        ( int-power-Large-Group G m x)
        ( int-power-Large-Group G n x)
    distributive-int-power-add-Large-Group {l} =
      distributive-integer-power-add-Group (group-Large-Group G l)
```

### The integer power `x⁻ᵏ` is the inverse of the integer power `xᵏ`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    int-power-neg-Large-Group :
      {l : Level} (k : ℤ) (x : type-Large-Group G l) →
      int-power-Large-Group G (neg-ℤ k) x ＝
      inv-Large-Group G (int-power-Large-Group G k x)
    int-power-neg-Large-Group {l} =
      integer-power-neg-Group (group-Large-Group G l)
```

### `xᵏ⁺¹ = xᵏx` and `xᵏ⁺¹ = xxᵏ`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    int-power-succ-Large-Group :
      {l : Level} (k : ℤ) (x : type-Large-Group G l) →
      int-power-Large-Group G (succ-ℤ k) x ＝
      mul-Large-Group G (int-power-Large-Group G k x) x
    int-power-succ-Large-Group {l} =
      integer-power-succ-Group (group-Large-Group G l)

    int-power-succ-Large-Group' :
      {l : Level} (k : ℤ) (x : type-Large-Group G l) →
      int-power-Large-Group G (succ-ℤ k) x ＝
      mul-Large-Group G x (int-power-Large-Group G k x)
    int-power-succ-Large-Group' {l} =
      integer-power-succ-Group' (group-Large-Group G l)
```

### `xᵏ⁻¹ = xᵏx⁻¹` and `xᵏ⁻¹ = x⁻¹xᵏ`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    int-power-pred-Large-Group :
      {l : Level} (k : ℤ) (x : type-Large-Group G l) →
      int-power-Large-Group G (pred-ℤ k) x ＝
      mul-Large-Group G (int-power-Large-Group G k x) (inv-Large-Group G x)
    int-power-pred-Large-Group {l} =
      integer-power-pred-Group (group-Large-Group G l)

    int-power-pred-Large-Group' :
      {l : Level} (k : ℤ) (x : type-Large-Group G l) →
      int-power-Large-Group G (pred-ℤ k) x ＝
      mul-Large-Group G (inv-Large-Group G x) (int-power-Large-Group G k x)
    int-power-pred-Large-Group' {l} =
      integer-power-pred-Group' (group-Large-Group G l)
```

### `1ᵏ ＝ 1`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    raise-int-power-unit-Large-Group :
      (l : Level) (k : ℤ) →
      int-power-Large-Group G k (raise-unit-Large-Group G l) ＝
      raise-unit-Large-Group G l
    raise-int-power-unit-Large-Group l =
      integer-power-unit-Group (group-Large-Group G l)
```

### If `x` commutes with `y` then so do their integer powers

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  (let _*_ = mul-Large-Group G)
  (let mul-inv = inv-Large-Group G)
  (let
    _^_ : {l : Level} → type-Large-Group G l → ℤ → type-Large-Group G l
    x ^ k = int-power-Large-Group G k x)
  where

  abstract
    commute-int-powers-Large-Group' :
      {l1 l2 : Level} (k : ℤ) →
      (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      (mul-Large-Group G x y ＝ mul-Large-Group G y x) →
      mul-Large-Group G (int-power-Large-Group G k x) y ＝
      mul-Large-Group G y (int-power-Large-Group G k x)
    commute-int-powers-Large-Group' {l1} {l2} n x y xy=yx =
      let
        x⁻¹y=yx⁻¹ =
          is-injective-emb
            ( emb-left-mul-Large-Group G (l1 ⊔ l2) x)
            ( equational-reasoning
              x * (mul-inv x * y)
              ＝ raise-Large-Group G l1 y
                by cancel-left-mul-div-Large-Group G x y
              ＝ (y * x) * mul-inv x
                by inv (cancel-right-mul-div-Large-Group G x y)
              ＝ (x * y) * mul-inv x
                by ap-mul-Large-Group G (inv xy=yx) refl
              ＝ x * (y * mul-inv x)
                by associative-mul-Large-Group G _ _ _)
        nonneg-case n =
          equational-reasoning
            (x ^ int-ℕ n) * y
            ＝ power-Large-Group G n x * y
              by ap-mul-Large-Group G (int-power-int-Large-Group G n x) refl
            ＝ y * power-Large-Group G n x
              by
                commute-powers-Large-Monoid'
                  ( large-monoid-Large-Group G)
                  ( n)
                  ( xy=yx)
            ＝ y * (x ^ int-ℕ n)
              by
                ap-mul-Large-Group G
                  ( refl)
                  ( inv (int-power-int-Large-Group G n x))
      in
        ind-ℤ
          ( λ k → (x ^ k) * y ＝ y * (x ^ k))
          ( equational-reasoning
            (x ^ neg-one-ℤ) * y
            ＝ mul-inv x * y
              by ap-mul-Large-Group G (int-power-neg-one-Large-Group G x) refl
            ＝ y * mul-inv x
              by x⁻¹y=yx⁻¹
            ＝ y * (x ^ neg-one-ℤ)
              by
                ap-mul-Large-Group G
                  ( refl)
                  ( inv (int-power-neg-one-Large-Group G x)))
          ( λ n x⁻ⁿy=yx⁻ⁿ →
            equational-reasoning
              (x ^ in-neg-ℤ (succ-ℕ n)) * y
              ＝ ((x ^ in-neg-ℤ n) * mul-inv x) * y
                by
                  ap-mul-Large-Group G
                    ( int-power-pred-Large-Group G (in-neg-ℤ n) x)
                    ( refl)
              ＝ (x ^ in-neg-ℤ n) * (mul-inv x * y)
                by associative-mul-Large-Group G _ _ _
              ＝ (x ^ in-neg-ℤ n) * (y * mul-inv x)
                by ap-mul-Large-Group G refl x⁻¹y=yx⁻¹
              ＝ ((x ^ in-neg-ℤ n) * y) * mul-inv x
                by inv (associative-mul-Large-Group G _ _ _)
              ＝ (y * (x ^ in-neg-ℤ n)) * mul-inv x
                by ap-mul-Large-Group G x⁻ⁿy=yx⁻ⁿ refl
              ＝ y * ((x ^ in-neg-ℤ n) * mul-inv x)
                by associative-mul-Large-Group G _ _ _
              ＝ y * (x ^ in-neg-ℤ (succ-ℕ n))
                by
                  ap-mul-Large-Group G
                    ( refl)
                    ( inv (int-power-pred-Large-Group G (in-neg-ℤ n) x)))
          ( nonneg-case 0)
          ( nonneg-case 1)
          ( λ n _ → nonneg-case (succ-ℕ (succ-ℕ n)))
          ( n)

    commute-int-powers-Large-Group'' :
      {l1 l2 : Level} (k : ℤ) →
      (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      (mul-Large-Group G x y ＝ mul-Large-Group G y x) →
      mul-Large-Group G x (int-power-Large-Group G k y) ＝
      mul-Large-Group G (int-power-Large-Group G k y) x
    commute-int-powers-Large-Group'' {l1} {l2} n x y xy=yx =
      let
        xy⁻¹=y⁻¹x =
          is-injective-emb
            ( emb-right-mul-Large-Group G (l1 ⊔ l2) y)
            ( equational-reasoning
              (x * mul-inv y) * y
              ＝ raise-Large-Group G l2 x
                by cancel-right-div-mul-Large-Group G y x
              ＝ mul-inv y * (y * x)
                by inv (cancel-left-div-mul-Large-Group G y x)
              ＝ mul-inv y * (x * y)
                by ap-mul-Large-Group G refl (inv xy=yx)
              ＝ (mul-inv y * x) * y
                by inv (associative-mul-Large-Group G _ _ _))
        nonneg-case n =
          equational-reasoning
            x * (y ^ int-ℕ n)
            ＝ x * power-Large-Group G n y
              by ap-mul-Large-Group G refl (int-power-int-Large-Group G n y)
            ＝ power-Large-Group G n y * x
              by
                commute-powers-Large-Monoid''
                  ( large-monoid-Large-Group G)
                  ( n)
                  ( xy=yx)
            ＝ (y ^ int-ℕ n) * x
              by
                ap-mul-Large-Group G
                  ( inv (int-power-int-Large-Group G n y))
                  ( refl)
      in
        ind-ℤ
          ( λ k →
            mul-Large-Group G x (int-power-Large-Group G k y) ＝
            mul-Large-Group G (int-power-Large-Group G k y) x)
          ( equational-reasoning
            x * (y ^ neg-one-ℤ)
            ＝ x * mul-inv y
              by ap-mul-Large-Group G refl (int-power-neg-one-Large-Group G y)
            ＝ mul-inv y * x
              by xy⁻¹=y⁻¹x
            ＝ (y ^ neg-one-ℤ) * x
              by
                ap-mul-Large-Group G
                  ( inv (int-power-neg-one-Large-Group G y))
                  ( refl))
          ( λ n xy⁻ⁿ=y⁻ⁿx →
            equational-reasoning
              x * (y ^ in-neg-ℤ (succ-ℕ n))
              ＝ x * (mul-inv y * (y ^ in-neg-ℤ n))
                by
                  ap-mul-Large-Group G
                    ( refl)
                    ( int-power-pred-Large-Group' G (in-neg-ℤ n) y)
              ＝ (x * mul-inv y) * (y ^ in-neg-ℤ n)
                by inv (associative-mul-Large-Group G _ _ _)
              ＝ (mul-inv y * x) * (y ^ in-neg-ℤ n)
                by ap-mul-Large-Group G xy⁻¹=y⁻¹x refl
              ＝ mul-inv y * (x * (y ^ in-neg-ℤ n))
                by associative-mul-Large-Group G _ _ _
              ＝ mul-inv y * ((y ^ in-neg-ℤ n) * x)
                by ap-mul-Large-Group G refl xy⁻ⁿ=y⁻ⁿx
              ＝ (mul-inv y * (y ^ in-neg-ℤ n)) * x
                by inv (associative-mul-Large-Group G _ _ _)
              ＝ (y ^ in-neg-ℤ (succ-ℕ n)) * x
                by
                  ap-mul-Large-Group G
                    ( inv (int-power-pred-Large-Group' G (in-neg-ℤ n) y))
                    ( refl))
          ( nonneg-case 0)
          ( nonneg-case 1)
          ( λ n _ → nonneg-case (succ-ℕ (succ-ℕ n)))
          ( n)

    commute-int-powers-Large-Group :
      {l1 l2 : Level} (k l : ℤ) →
      {x : type-Large-Group G l1} {y : type-Large-Group G l2} →
      ( mul-Large-Group G x y ＝ mul-Large-Group G y x) →
      ( mul-Large-Group G
          ( int-power-Large-Group G k x)
          ( int-power-Large-Group G l y) ＝
        mul-Large-Group G
          ( int-power-Large-Group G l y)
          ( int-power-Large-Group G k x))
    commute-int-powers-Large-Group k l {x} {y} xy=yx =
      commute-int-powers-Large-Group' k x _
        ( commute-int-powers-Large-Group'' l x y xy=yx)
```

### If `x` commutes with `y`, then integer powers distribute over the product of `x` and `y`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    distributive-int-power-mul-Large-Group :
      {l1 l2 : Level} (k : ℤ) →
      (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      ( mul-Large-Group G x y ＝ mul-Large-Group G y x) →
      int-power-Large-Group G k (mul-Large-Group G x y) ＝
      mul-Large-Group G
        ( int-power-Large-Group G k x)
        ( int-power-Large-Group G k y)
    distributive-int-power-mul-Large-Group {l1} {l2} l x y xy=yx =
      let
        _^_ : {l : Level} → type-Large-Group G l → ℤ → type-Large-Group G l
        x ^ k = int-power-Large-Group G k x
        _*_ = mul-Large-Group G
        mul-inv = inv-Large-Group G
        nonneg-case n =
          equational-reasoning
            (x * y) ^ int-ℕ n
            ＝ power-Large-Group G n (x * y)
              by int-power-int-Large-Group G n (x * y)
            ＝ power-Large-Group G n x * power-Large-Group G n y
              by distributive-power-mul-Large-Group G n xy=yx
            ＝ (x ^ int-ℕ n) * (y ^ int-ℕ n)
              by
                ap-mul-Large-Group G
                  ( inv (int-power-int-Large-Group G n x))
                  ( inv (int-power-int-Large-Group G n y))
        x⁻¹y⁻¹=⟨xy⟩⁻¹ =
          eq-sim-Large-Group G _ _
            ( unique-right-inv-Large-Group G (x * y) (mul-inv x * mul-inv y)
              ( equational-reasoning
                (x * y) * (mul-inv x * mul-inv y)
                ＝ (y * x) * (mul-inv x * mul-inv y)
                  by ap-mul-Large-Group G xy=yx refl
                ＝ y * (x * (mul-inv x * mul-inv y))
                  by associative-mul-Large-Group G _ _ _
                ＝ y * raise-Large-Group G l1 (mul-inv y)
                  by
                    ap-mul-Large-Group G
                      ( refl)
                      ( cancel-left-mul-div-Large-Group G x _)
                ＝ raise-Large-Group G l1 (y * mul-inv y)
                  by mul-raise-right-Large-Group G _ _
                ＝ raise-Large-Group G l1 (raise-unit-Large-Group G l2)
                  by
                    ap
                      ( raise-Large-Group G l1)
                      ( sim-right-inverse-law-mul-Large-Group G y)
                ＝ raise-unit-Large-Group G (l1 ⊔ l2)
                  by raise-raise-Large-Group G _))
      in
        ind-ℤ
          ( λ k →
            int-power-Large-Group G k (mul-Large-Group G x y) ＝
            mul-Large-Group G
              ( int-power-Large-Group G k x)
              ( int-power-Large-Group G k y))
          ( equational-reasoning
            (x * y) ^ neg-one-ℤ
            ＝ mul-inv (x * y)
              by int-power-neg-one-Large-Group G _
            ＝ mul-inv x * mul-inv y
              by inv x⁻¹y⁻¹=⟨xy⟩⁻¹
            ＝ (x ^ neg-one-ℤ) * (y ^ neg-one-ℤ)
              by
                ap-mul-Large-Group G
                  ( inv (int-power-neg-one-Large-Group G x))
                  ( inv (int-power-neg-one-Large-Group G y)))
          ( λ n ⟨xy⟩⁻ⁿ=x⁻ⁿy⁻ⁿ →

            equational-reasoning
              (x * y) ^ in-neg-ℤ (succ-ℕ n)
              ＝ ((x * y) ^ in-neg-ℤ n) * mul-inv (x * y)
                by int-power-pred-Large-Group G (in-neg-ℤ n) (x * y)
              ＝ (( x ^ in-neg-ℤ n) * (y ^ in-neg-ℤ n)) * (mul-inv x * mul-inv y)
                by
                  ap-mul-Large-Group G ⟨xy⟩⁻ⁿ=x⁻ⁿy⁻ⁿ (inv x⁻¹y⁻¹=⟨xy⟩⁻¹)
              ＝ (x ^ in-neg-ℤ n) * ((y ^ in-neg-ℤ n) * (mul-inv x * mul-inv y))
                by
                  associative-mul-Large-Group G _ _ _
              ＝ (x ^ in-neg-ℤ n) * (((y ^ in-neg-ℤ n) * mul-inv x) * mul-inv y)
                by
                  ap-mul-Large-Group G
                    ( refl)
                    ( inv (associative-mul-Large-Group G _ _ _))
              ＝
                (x ^ in-neg-ℤ n) *
                (((y ^ in-neg-ℤ n) * (x ^ neg-one-ℤ)) * mul-inv y)
                by
                  ap-mul-Large-Group G
                    ( refl)
                    ( ap-mul-Large-Group G
                      ( ap-mul-Large-Group G
                        ( refl)
                        ( inv (int-power-neg-one-Large-Group G x)))
                      ( refl))
              ＝
                (x ^ in-neg-ℤ n) *
                (((x ^ neg-one-ℤ) * (y ^ in-neg-ℤ n)) * mul-inv y)
                by
                  ap-mul-Large-Group G
                    ( refl)
                    ( ap-mul-Large-Group G
                      ( commute-int-powers-Large-Group G
                        ( in-neg-ℤ n)
                        ( neg-one-ℤ)
                        ( inv xy=yx))
                      ( refl))
              ＝
                (x ^ in-neg-ℤ n) *
                ((x ^ neg-one-ℤ) * ((y ^ in-neg-ℤ n) * mul-inv y))
                by
                  ap-mul-Large-Group G
                    ( refl)
                    ( associative-mul-Large-Group G _ _ _)
              ＝
                ((x ^ in-neg-ℤ n) * (x ^ neg-one-ℤ)) *
                ((y ^ in-neg-ℤ n) * mul-inv y)
                by
                  inv (associative-mul-Large-Group G _ _ _)
              ＝ ((x ^ in-neg-ℤ n) * mul-inv x) * (y ^ in-neg-ℤ (succ-ℕ n))
                  by
                    ap-mul-Large-Group G
                      ( ap-mul-Large-Group G
                        ( refl)
                        ( int-power-neg-one-Large-Group G x))
                      ( inv (int-power-pred-Large-Group G (in-neg-ℤ n) y))
              ＝ (x ^ in-neg-ℤ (succ-ℕ n)) * (y ^ in-neg-ℤ (succ-ℕ n))
                by
                  ap-mul-Large-Group G
                    ( inv (int-power-pred-Large-Group G (in-neg-ℤ n) x))
                    ( refl))
          ( nonneg-case 0)
          ( nonneg-case 1)
          ( λ n _ → nonneg-case (succ-ℕ (succ-ℕ n)))
          ( l)
```

### Powers by products of integers are iterated integer powers

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    int-power-mul-Large-Group :
      {l1 : Level} (k l : ℤ) (x : type-Large-Group G l1) →
      int-power-Large-Group G (k *ℤ l) x ＝
      int-power-Large-Group G l (int-power-Large-Group G k x)
    int-power-mul-Large-Group {l1} =
      integer-power-mul-Group (group-Large-Group G l1)
```

## See also

- [Natural powers of elements of large groups](group-theory.powers-of-elements-large-groups.md)
- [Integer powers of elements of small groups](group-theory.integer-powers-of-elements-groups.md)
