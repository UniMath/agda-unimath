# Powers of elements in semirings

```agda
module ring-theory.powers-of-elements-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.semirings
```

</details>

## Idea

The power operation on a semiring is the map `n x ↦ xⁿ`, which is defined by iteratively multiplying `x` with itself `n` times.

## Definition

```agda
power-Semiring :
  {l : Level} (R : Semiring l) → ℕ → type-Semiring R → type-Semiring R
power-Semiring R zero-ℕ x = one-Semiring R
power-Semiring R (succ-ℕ zero-ℕ) x = x
power-Semiring R (succ-ℕ (succ-ℕ n)) x =
  mul-Semiring R (power-Semiring R (succ-ℕ n) x) x
```

## Properties

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {l : Level} (R : Semiring l)
  where

  power-succ-Semiring :
    (n : ℕ) (x : type-Semiring R) →
    power-Semiring R (succ-ℕ n) x ＝ mul-Semiring R (power-Semiring R n x) x
  power-succ-Semiring zero-ℕ x = inv (left-unit-law-mul-Semiring R x)
  power-succ-Semiring (succ-ℕ n) x = refl
```

### If `x` commutes with `y` then so do their powers

```agda
module _
  {l : Level} (R : Semiring l)
  where

  commute-powers-Semiring' :
    (n : ℕ) {x y : type-Semiring R} →
    ( mul-Semiring R x y ＝ mul-Semiring R y x) →
    ( mul-Semiring R (power-Semiring R n x) y) ＝
    ( mul-Semiring R y (power-Semiring R n x))
  commute-powers-Semiring' zero-ℕ H =
    left-unit-law-mul-Semiring R _ ∙ inv (right-unit-law-mul-Semiring R _)
  commute-powers-Semiring' (succ-ℕ zero-ℕ) {x} {y} H = H
  commute-powers-Semiring' (succ-ℕ (succ-ℕ n)) {x} {y} H =
    ( associative-mul-Semiring R (power-Semiring R (succ-ℕ n) x) x y) ∙
    ( ( ap (mul-Semiring R (power-Semiring R (succ-ℕ n) x)) H) ∙
      ( ( inv
          ( associative-mul-Semiring R (power-Semiring R (succ-ℕ n) x) y x)) ∙
        ( ( ap (mul-Semiring' R x) (commute-powers-Semiring' (succ-ℕ n) H)) ∙
          ( associative-mul-Semiring R y (power-Semiring R (succ-ℕ n) x) x))))

  commute-powers-Semiring :
    (m n : ℕ) {x y : type-Semiring R} →
    ( mul-Semiring R x y ＝ mul-Semiring R y x) →
    ( mul-Semiring R
      ( power-Semiring R m x)
      ( power-Semiring R n y)) ＝
    ( mul-Semiring R
      ( power-Semiring R n y)
      ( power-Semiring R m x))
  commute-powers-Semiring zero-ℕ zero-ℕ H = refl
  commute-powers-Semiring zero-ℕ (succ-ℕ n) H =
    ( left-unit-law-mul-Semiring R (power-Semiring R (succ-ℕ n) _)) ∙
    ( inv (right-unit-law-mul-Semiring R (power-Semiring R (succ-ℕ n) _)))
  commute-powers-Semiring (succ-ℕ m) zero-ℕ H =
    ( right-unit-law-mul-Semiring R (power-Semiring R (succ-ℕ m) _)) ∙
    ( inv (left-unit-law-mul-Semiring R (power-Semiring R (succ-ℕ m) _)))
  commute-powers-Semiring (succ-ℕ m) (succ-ℕ n) {x} {y} H =
    ( ap-mul-Semiring R
      ( power-succ-Semiring R m x)
      ( power-succ-Semiring R n y)) ∙
    ( ( associative-mul-Semiring R
        ( power-Semiring R m x)
        ( x)
        ( mul-Semiring R (power-Semiring R n y) y)) ∙
      ( ( ap
          ( mul-Semiring R (power-Semiring R m x))
          ( ( inv (associative-mul-Semiring R x (power-Semiring R n y) y)) ∙
            ( ( ap
                ( mul-Semiring' R y)
                ( inv (commute-powers-Semiring' n (inv H)))) ∙
              ( ( associative-mul-Semiring R (power-Semiring R n y) x y) ∙
                ( ( ap (mul-Semiring R (power-Semiring R n y)) H) ∙
                  ( inv
                    ( associative-mul-Semiring R
                      ( power-Semiring R n y)
                      ( y)
                      ( x)))))))) ∙
        ( ( inv
            ( associative-mul-Semiring R
              ( power-Semiring R m x)
              ( mul-Semiring R (power-Semiring R n y) y)
              ( x))) ∙
          ( ( ap
              ( mul-Semiring' R x)
              ( ( inv
                  ( associative-mul-Semiring R
                    ( power-Semiring R m x)
                    ( power-Semiring R n y)
                    ( y))) ∙
                ( ( ap
                    ( mul-Semiring' R y)
                    ( commute-powers-Semiring m n H)) ∙
                  ( ( associative-mul-Semiring R
                      ( power-Semiring R n y)
                      ( power-Semiring R m x)
                      ( y)) ∙
                    ( ( ap
                        ( mul-Semiring R (power-Semiring R n y))
                        ( commute-powers-Semiring' m H)) ∙
                      ( ( inv
                          ( associative-mul-Semiring R
                            ( power-Semiring R n y)
                            ( y)
                            ( power-Semiring R m x))) ∙
                        ( ap
                          ( mul-Semiring' R (power-Semiring R m x))
                          ( inv (power-succ-Semiring R n y))))))))) ∙
            ( ( associative-mul-Semiring R
                ( power-Semiring R (succ-ℕ n) y)
                ( power-Semiring R m x)
                ( x)) ∙
              ( ap
                ( mul-Semiring R (power-Semiring R (succ-ℕ n) y))
                ( inv (power-succ-Semiring R m x))))))))
```
