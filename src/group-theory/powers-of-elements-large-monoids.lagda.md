# Powers of elements in large monoids

```agda
module group-theory.powers-of-elements-large-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.large-monoids
open import group-theory.powers-of-elements-monoids
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="raising an element of a large monoid to a natural number power" Agda=power-Large-Monoid}}
on a [large monoid](group-theory.large-monoids.md) is the map `n x ↦ xⁿ`, which
is defined by [iteratively](foundation.iterating-functions.md) multiplying `x`
with itself `n` times.

## Definitions

### Powers of elements of monoids

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  power-Large-Monoid :
    {l : Level} → ℕ → type-Large-Monoid M l → type-Large-Monoid M l
  power-Large-Monoid {l} = power-Monoid (monoid-Large-Monoid M l)
```

## Properties

### The power operation preserves similarity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  abstract
    preserves-sim-power-Large-Monoid :
      {l1 l2 : Level} (n : ℕ) →
      (x : type-Large-Monoid M l1) (y : type-Large-Monoid M l2) →
      sim-Large-Monoid M x y →
      sim-Large-Monoid M (power-Large-Monoid M n x) (power-Large-Monoid M n y)
    preserves-sim-power-Large-Monoid {l1} {l2} 0 _ _ _ =
      let
        open similarity-reasoning-Large-Monoid M
      in
        similarity-reasoning
          raise-unit-Large-Monoid M l1
          ~ unit-Large-Monoid M
            by symmetric-sim-Large-Monoid M _ _ (sim-raise-Large-Monoid M _ _)
          ~ raise-unit-Large-Monoid M l2
            by sim-raise-Large-Monoid M _ _
    preserves-sim-power-Large-Monoid 1 _ _ x~y = x~y
    preserves-sim-power-Large-Monoid (succ-ℕ (succ-ℕ n)) x y x~y =
      preserves-sim-mul-Large-Monoid M
        ( power-Large-Monoid M (succ-ℕ n) x)
        ( power-Large-Monoid M (succ-ℕ n) y)
        ( preserves-sim-power-Large-Monoid (succ-ℕ n) x y x~y)
        ( x)
        ( y)
        ( x~y)
```

### `1ⁿ = 1`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  abstract
    raise-power-unit-Large-Monoid :
      (l : Level) (n : ℕ) →
      power-Large-Monoid M n (raise-unit-Large-Monoid M l) ＝
      raise-unit-Large-Monoid M l
    raise-power-unit-Large-Monoid l =
      power-unit-Monoid (monoid-Large-Monoid M l)

    power-unit-Large-Monoid :
      (n : ℕ) →
      power-Large-Monoid M n (unit-Large-Monoid M) ＝ unit-Large-Monoid M
    power-unit-Large-Monoid n =
      tr
        ( λ x → power-Large-Monoid M n x ＝ x)
        ( raise-unit-lzero-Large-Monoid M)
        ( raise-power-unit-Large-Monoid lzero n)
```

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  abstract
    power-succ-Large-Monoid :
      {l : Level} (n : ℕ) (x : type-Large-Monoid M l) →
      power-Large-Monoid M (succ-ℕ n) x ＝
      mul-Large-Monoid M (power-Large-Monoid M n x) x
    power-succ-Large-Monoid {l} = power-succ-Monoid (monoid-Large-Monoid M l)
```

### `xⁿ⁺¹ = xxⁿ`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  abstract
    power-succ-Large-Monoid' :
      {l : Level} (n : ℕ) (x : type-Large-Monoid M l) →
      power-Large-Monoid M (succ-ℕ n) x ＝
      mul-Large-Monoid M x (power-Large-Monoid M n x)
    power-succ-Large-Monoid' {l} =
      power-succ-Monoid' (monoid-Large-Monoid M l)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  abstract
    distributive-power-add-Large-Monoid :
      {l : Level} (m n : ℕ) {x : type-Large-Monoid M l} →
      power-Large-Monoid M (m +ℕ n) x ＝
      mul-Large-Monoid M (power-Large-Monoid M m x) (power-Large-Monoid M n x)
    distributive-power-add-Large-Monoid {l} =
      distributive-power-add-Monoid (monoid-Large-Monoid M l)
```

### If `x` commutes with `y` then so do their powers

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  private
    _*_ = mul-Large-Monoid M

  open similarity-reasoning-Large-Monoid M

  abstract
    commute-powers-Large-Monoid' :
      {l1 l2 : Level} (n : ℕ) →
      {x : type-Large-Monoid M l1} {y : type-Large-Monoid M l2} →
      ( mul-Large-Monoid M x y ＝ mul-Large-Monoid M y x) →
      ( mul-Large-Monoid M (power-Large-Monoid M n x) y) ＝
      ( mul-Large-Monoid M y (power-Large-Monoid M n x))
    commute-powers-Large-Monoid' {l1} {l2} 0 {x} {y} H =
      equational-reasoning
        raise-unit-Large-Monoid M l1 * y
        ＝ raise-Large-Monoid M l1 y
          by raise-left-unit-law-Large-Monoid M y
        ＝ y * raise-unit-Large-Monoid M l1
          by inv (raise-right-unit-law-Large-Monoid M y)
    commute-powers-Large-Monoid' 1 H = H
    commute-powers-Large-Monoid' (succ-ℕ n@(succ-ℕ _)) {x} {y} H =
      equational-reasoning
        power-Large-Monoid M (succ-ℕ n) x * y
        ＝
          power-Large-Monoid M n x * (x * y)
          by associative-mul-Large-Monoid M _ _ _
        ＝
          power-Large-Monoid M n x * (y * x)
          by ap-mul-Large-Monoid M refl H
        ＝
          (power-Large-Monoid M n x * y) * x
          by inv (associative-mul-Large-Monoid M _ _ _)
        ＝
          (y * power-Large-Monoid M n x) * x
          by ap-mul-Large-Monoid M (commute-powers-Large-Monoid' n H) refl
        ＝ y * power-Large-Monoid M (succ-ℕ n) x
          by associative-mul-Large-Monoid M _ _ _

    commute-powers-Large-Monoid'' :
      {l1 l2 : Level} (n : ℕ) →
      {x : type-Large-Monoid M l1} {y : type-Large-Monoid M l2} →
      ( mul-Large-Monoid M x y ＝ mul-Large-Monoid M y x) →
      ( mul-Large-Monoid M x (power-Large-Monoid M n y)) ＝
      ( mul-Large-Monoid M (power-Large-Monoid M n y) x)
    commute-powers-Large-Monoid'' {l1} {l2} 0 {x} {y} H =
      equational-reasoning
        x * raise-unit-Large-Monoid M l2
        ＝ raise-Large-Monoid M l2 x
          by raise-right-unit-law-Large-Monoid M x
        ＝ raise-unit-Large-Monoid M l2 * x
          by inv (raise-left-unit-law-Large-Monoid M x)
    commute-powers-Large-Monoid'' 1 H = H
    commute-powers-Large-Monoid'' (succ-ℕ n@(succ-ℕ _)) {x} {y} H =
      equational-reasoning
        x * power-Large-Monoid M (succ-ℕ n) y
        ＝ x * (y * power-Large-Monoid M n y)
          by ap-mul-Large-Monoid M refl (power-succ-Large-Monoid' M n y)
        ＝ (x * y) * power-Large-Monoid M n y
          by inv (associative-mul-Large-Monoid M _ _ _)
        ＝ (y * x) * power-Large-Monoid M n y
          by ap-mul-Large-Monoid M H refl
        ＝ y * (x * power-Large-Monoid M n y)
          by associative-mul-Large-Monoid M _ _ _
        ＝ y * (power-Large-Monoid M n y * x)
          by ap-mul-Large-Monoid M refl (commute-powers-Large-Monoid'' n H)
        ＝ (y * power-Large-Monoid M n y) * x
          by inv (associative-mul-Large-Monoid M _ _ _)
        ＝ power-Large-Monoid M (succ-ℕ n) y * x
          by ap-mul-Large-Monoid M (inv (power-succ-Large-Monoid' M n y)) refl

    commute-powers-Large-Monoid :
      {l1 l2 : Level} (m n : ℕ) →
      {x : type-Large-Monoid M l1} {y : type-Large-Monoid M l2} →
      ( mul-Large-Monoid M x y ＝ mul-Large-Monoid M y x) →
      ( mul-Large-Monoid M
        ( power-Large-Monoid M m x)
        ( power-Large-Monoid M n y)) ＝
      ( mul-Large-Monoid M
        ( power-Large-Monoid M n y)
        ( power-Large-Monoid M m x))
    commute-powers-Large-Monoid {l1} {l2} m n {x} {y} H =
      commute-powers-Large-Monoid'
        ( m)
        ( commute-powers-Large-Monoid'' n H)
```

### If `x` commutes with `y`, their powers distribute over the product of `x` and `y`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  open similarity-reasoning-Large-Monoid M

  private
    _*_ = mul-Large-Monoid M

  abstract
    distributive-power-mul-Large-Monoid :
      {l1 l2 : Level} (n : ℕ) →
      {x : type-Large-Monoid M l1} {y : type-Large-Monoid M l2} →
      (mul-Large-Monoid M x y ＝ mul-Large-Monoid M y x) →
      power-Large-Monoid M n (mul-Large-Monoid M x y) ＝
      mul-Large-Monoid M (power-Large-Monoid M n x) (power-Large-Monoid M n y)
    distributive-power-mul-Large-Monoid {l1} {l2} 0 _ =
      inv
        ( equational-reasoning
            raise-unit-Large-Monoid M l1 * raise-unit-Large-Monoid M l2
            ＝ raise-Large-Monoid M l1 (raise-unit-Large-Monoid M l2)
              by raise-left-unit-law-Large-Monoid M _
            ＝ raise-unit-Large-Monoid M (l1 ⊔ l2)
              by raise-raise-Large-Monoid M _)
    distributive-power-mul-Large-Monoid 1 _ = refl
    distributive-power-mul-Large-Monoid (succ-ℕ n@(succ-ℕ _)) {x} {y} H =
      equational-reasoning
        power-Large-Monoid M n (x * y) * (x * y)
        ＝ (power-Large-Monoid M n x * power-Large-Monoid M n y) * (x * y)
          by
            ap-mul-Large-Monoid M
              ( distributive-power-mul-Large-Monoid n H)
              ( refl)
        ＝ power-Large-Monoid M n x * (power-Large-Monoid M n y * (x * y))
          by associative-mul-Large-Monoid M _ _ _
        ＝ power-Large-Monoid M n x * ((power-Large-Monoid M n y * x) * y)
          by
            ap-mul-Large-Monoid M
              ( refl)
              ( inv (associative-mul-Large-Monoid M _ _ _))
        ＝ power-Large-Monoid M n x * ((x * power-Large-Monoid M n y) * y)
          by
            ap-mul-Large-Monoid M
              ( refl)
              ( ap-mul-Large-Monoid M
                ( commute-powers-Large-Monoid' M n (inv H))
                ( refl))
        ＝ power-Large-Monoid M n x * (x * power-Large-Monoid M (succ-ℕ n) y)
          by
            ap-mul-Large-Monoid M
              ( refl)
              ( associative-mul-Large-Monoid M _ _ _)
        ＝ power-Large-Monoid M (succ-ℕ n) x * power-Large-Monoid M (succ-ℕ n) y
          by inv (associative-mul-Large-Monoid M _ _ _)
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  abstract
    power-mul-Large-Monoid :
      {l : Level} (m n : ℕ) {x : type-Large-Monoid M l} →
      power-Large-Monoid M (m *ℕ n) x ＝
      power-Large-Monoid M n (power-Large-Monoid M m x)
    power-mul-Large-Monoid {l} = power-mul-Monoid (monoid-Large-Monoid M l)
```

### Iterated powers commute

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  abstract
    commute-power-Large-Monoid :
      {l : Level} (m n : ℕ) (x : type-Large-Monoid M l) →
      power-Large-Monoid M m (power-Large-Monoid M n x) ＝
      power-Large-Monoid M n (power-Large-Monoid M m x)
    commute-power-Large-Monoid m n x =
      equational-reasoning
        power-Large-Monoid M m (power-Large-Monoid M n x)
        ＝ power-Large-Monoid M (n *ℕ m) x
          by inv (power-mul-Large-Monoid M n m)
        ＝ power-Large-Monoid M (m *ℕ n) x
          by ap (λ k → power-Large-Monoid M k x) (commutative-mul-ℕ n m)
        ＝ power-Large-Monoid M n (power-Large-Monoid M m x)
          by power-mul-Large-Monoid M m n
```
