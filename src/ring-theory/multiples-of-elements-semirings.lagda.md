# Multiples of elements in semirings

```agda
module ring-theory.multiples-of-elements-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.powers-of-elements-commutative-monoids

open import ring-theory.semirings
```

</details>

## Idea

For any [semiring](ring-theory.semirings.md) `R` there is a multiplication
operation `ℕ → R → R`, which we write informally as `n x ↦ n · x`, called taking
a
{{#concept "multiple" Disambiguation="of an element of a semiring, natural number" Agda=multiple-Semiring}}
of `x`. This operation is defined by
[iteratively](foundation.iterating-functions.md) adding `x` with itself `n`
times.

## Definition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  multiple-Semiring : ℕ → type-Semiring R → type-Semiring R
  multiple-Semiring =
    power-Commutative-Monoid (additive-commutative-monoid-Semiring R)

  ap-multiple-Semiring :
    {m n : ℕ} {x y : type-Semiring R} →
    (m ＝ n) → (x ＝ y) →
    multiple-Semiring m x ＝ multiple-Semiring n y
  ap-multiple-Semiring p q = ap-binary multiple-Semiring p q
```

## Properties

```agda
module _
  {l : Level} (R : Semiring l)
  where

  abstract
    left-zero-law-multiple-Semiring :
      (x : type-Semiring R) → multiple-Semiring R 0 x ＝ zero-Semiring R
    left-zero-law-multiple-Semiring x = refl

    right-zero-law-multiple-Semiring :
      (n : ℕ) → multiple-Semiring R n (zero-Semiring R) ＝ zero-Semiring R
    right-zero-law-multiple-Semiring =
      power-unit-Commutative-Monoid (additive-commutative-monoid-Semiring R)

    multiple-succ-Semiring :
      (n : ℕ) (x : type-Semiring R) →
      multiple-Semiring R (succ-ℕ n) x ＝
      add-Semiring R (multiple-Semiring R n x) x
    multiple-succ-Semiring =
      power-succ-Commutative-Monoid (additive-commutative-monoid-Semiring R)

    left-unit-law-multiple-Semiring :
      (x : type-Semiring R) → multiple-Semiring R 1 x ＝ x
    left-unit-law-multiple-Semiring x = refl

    left-mul-multiple-Semiring :
      (n : ℕ) (x y : type-Semiring R) →
      mul-Semiring R (multiple-Semiring R n x) y ＝
      multiple-Semiring R n (mul-Semiring R x y)
    left-mul-multiple-Semiring 0 x y = left-zero-law-mul-Semiring R y
    left-mul-multiple-Semiring 1 x y = refl
    left-mul-multiple-Semiring (succ-ℕ n@(succ-ℕ _)) x y =
      ( right-distributive-mul-add-Semiring R _ _ _) ∙
      ( ap-add-Semiring R (left-mul-multiple-Semiring n x y) refl)

    right-mul-multiple-Semiring :
      (n : ℕ) (x y : type-Semiring R) →
      mul-Semiring R x (multiple-Semiring R n y) ＝
      multiple-Semiring R n (mul-Semiring R x y)
    right-mul-multiple-Semiring 0 x y = right-zero-law-mul-Semiring R x
    right-mul-multiple-Semiring 1 x y = refl
    right-mul-multiple-Semiring (succ-ℕ n@(succ-ℕ _)) x y =
      ( left-distributive-mul-add-Semiring R _ _ _) ∙
      ( ap-add-Semiring R (right-mul-multiple-Semiring n x y) refl)

    left-distributive-multiple-add-Semiring :
      (n : ℕ) (x y : type-Semiring R) →
      multiple-Semiring R n (add-Semiring R x y) ＝
      add-Semiring R (multiple-Semiring R n x) (multiple-Semiring R n y)
    left-distributive-multiple-add-Semiring 0 x y =
      inv (left-unit-law-add-Semiring R _)
    left-distributive-multiple-add-Semiring 1 x y = refl
    left-distributive-multiple-add-Semiring (succ-ℕ n@(succ-ℕ _)) x y =
      equational-reasoning
        add-Semiring R
          ( multiple-Semiring R n (add-Semiring R x y))
          ( add-Semiring R x y)
        ＝
          add-Semiring R
            ( add-Semiring R
              ( multiple-Semiring R n x)
              ( multiple-Semiring R n y))
            ( add-Semiring R x y)
          by
            ap-add-Semiring R
              ( left-distributive-multiple-add-Semiring n x y)
              ( refl)
        ＝
          add-Semiring R
            ( multiple-Semiring R (succ-ℕ n) x)
            ( multiple-Semiring R (succ-ℕ n) y)
          by interchange-add-add-Semiring R _ _ _ _

    right-distributive-multiple-add-Semiring :
      (m n : ℕ) (x : type-Semiring R) →
      multiple-Semiring R (m +ℕ n) x ＝
      add-Semiring R (multiple-Semiring R m x) (multiple-Semiring R n x)
    right-distributive-multiple-add-Semiring m n x =
      distributive-power-add-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
        ( m)
        ( n)

    right-distributive-multiple-mul-Semiring :
      ( m n : ℕ) →
      ( multiple-Semiring R (m *ℕ n)) ~
      ( multiple-Semiring R m ∘ multiple-Semiring R n)
    right-distributive-multiple-mul-Semiring m n x =
      ( ap (λ k → multiple-Semiring R k x) (commutative-mul-ℕ m n)) ∙
      ( power-mul-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
        ( n)
        ( m))
```
