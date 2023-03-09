# Divisibility of integers

```agda
module elementary-number-theory.divisibility-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equational-reasoning
open import foundation.functions
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

An integer `d` divides an integer `x` if there is an integer `k` such that `mul-ℤ k d = x`. In other words, the type `div-ℤ d x` is the fiber `fib (mul-ℤ' d) x`.

## Definition

```agda
div-ℤ : ℤ → ℤ → UU lzero
div-ℤ d x = Σ ℤ (λ k → mul-ℤ k d ＝ x)

quotient-div-ℤ : (x y : ℤ) → div-ℤ x y → ℤ
quotient-div-ℤ x y H = pr1 H

eq-quotient-div-ℤ :
  (x y : ℤ) (H : div-ℤ x y) → mul-ℤ (quotient-div-ℤ x y H) x ＝ y
eq-quotient-div-ℤ x y H = pr2 H

eq-quotient-div-ℤ' :
  (x y : ℤ) (H : div-ℤ x y) → mul-ℤ x (quotient-div-ℤ x y H) ＝ y
eq-quotient-div-ℤ' x y H =
  commutative-mul-ℤ x (quotient-div-ℤ x y H) ∙ eq-quotient-div-ℤ x y H
```

## Properties

### The divisibility relation is a preorder

```agda
refl-div-ℤ : (x : ℤ) → div-ℤ x x
pr1 (refl-div-ℤ x) = one-ℤ
pr2 (refl-div-ℤ x) = left-unit-law-mul-ℤ x

trans-div-ℤ :
  (x y z : ℤ) → div-ℤ x y → div-ℤ y z → div-ℤ x z
pr1 (trans-div-ℤ x y z (pair d p) (pair e q)) = mul-ℤ e d
pr2 (trans-div-ℤ x y z (pair d p) (pair e q)) =
  ( associative-mul-ℤ e d x) ∙
    ( ( ap (mul-ℤ e) p) ∙
      ( q))
```

### Divisibility by a nonzero integer is a property

```agda
is-prop-div-ℤ : (d x : ℤ) → is-nonzero-ℤ d → is-prop (div-ℤ d x)
is-prop-div-ℤ d x f = is-prop-map-is-emb (is-emb-mul-ℤ' d f) x
```

### Every integer is divisible by 1

```agda
div-one-ℤ : (x : ℤ) → div-ℤ one-ℤ x
pr1 (div-one-ℤ x) = x
pr2 (div-one-ℤ x) = right-unit-law-mul-ℤ x
```

### Every integer divides 0

```agda
div-zero-ℤ : (x : ℤ) → div-ℤ x zero-ℤ
pr1 (div-zero-ℤ x) = zero-ℤ
pr2 (div-zero-ℤ x) = left-zero-law-mul-ℤ x
```

### Every integer that is divisible by 0 is 0.

```agda
is-zero-div-zero-ℤ :
  (x : ℤ) → div-ℤ zero-ℤ x → is-zero-ℤ x
is-zero-div-zero-ℤ x (pair d p) = inv p ∙ right-zero-law-mul-ℤ d
```
### If `k` divides `x` and `k` is 0 then `x` is 0

```agda
is-zero-is-zero-div-ℤ : (x k : ℤ) → div-ℤ k x → is-zero-ℤ k → is-zero-ℤ x
is-zero-is-zero-div-ℤ x .zero-ℤ k-div-x refl = is-zero-div-zero-ℤ x k-div-x
```

### If `x` divides both `y` and `z`, then it divides `y + z`

```agda
div-add-ℤ : (x y z : ℤ) → div-ℤ x y → div-ℤ x z → div-ℤ x (add-ℤ y z)
pr1 (div-add-ℤ x y z (pair d p) (pair e q)) = add-ℤ d e
pr2 (div-add-ℤ x y z (pair d p) (pair e q)) =
  ( right-distributive-mul-add-ℤ d e x) ∙
  ( ap-add-ℤ p q)
```

### If `x` divides `y` then `x` divides any multiple of `y`

```agda
div-mul-ℤ :
  (k x y : ℤ) → div-ℤ x y → div-ℤ x (mul-ℤ k y)
div-mul-ℤ k x y H =
  trans-div-ℤ x y (mul-ℤ k y) H (pair k refl)
```

### If `x` divides `y` then it divides `-y`

```agda
div-neg-ℤ : (x y : ℤ) → div-ℤ x y → div-ℤ x (neg-ℤ y)
pr1 (div-neg-ℤ x y (pair d p)) = neg-ℤ d
pr2 (div-neg-ℤ x y (pair d p)) = left-negative-law-mul-ℤ d x ∙ ap neg-ℤ p
```

### If `x` divides `y` then `-x` divides `y`

```agda
neg-div-ℤ : (x y : ℤ) → div-ℤ x y → div-ℤ (neg-ℤ x) y
pr1 (neg-div-ℤ x y (pair d p)) = neg-ℤ d
pr2 (neg-div-ℤ x y (pair d p)) =
  equational-reasoning
    mul-ℤ (neg-ℤ d) (neg-ℤ x)
    ＝ neg-ℤ (mul-ℤ d (neg-ℤ x))   by left-negative-law-mul-ℤ d (neg-ℤ x)
    ＝ neg-ℤ (neg-ℤ (mul-ℤ d x))   by ap neg-ℤ (right-negative-law-mul-ℤ d x)
    ＝ (mul-ℤ d x)                 by neg-neg-ℤ (mul-ℤ d x)
    ＝ y                           by p
```

### Multiplication preserves divisibility

```agda
preserves-div-mul-ℤ :
  (k x y : ℤ) → div-ℤ x y → div-ℤ (mul-ℤ k x) (mul-ℤ k y)
pr1 (preserves-div-mul-ℤ k x y (pair q p)) = q
pr2 (preserves-div-mul-ℤ k x y (pair q p)) =
  ( inv (associative-mul-ℤ q k x)) ∙
    ( ( ap (mul-ℤ' x) (commutative-mul-ℤ q k)) ∙
      ( ( associative-mul-ℤ k q x) ∙
        ( ap (mul-ℤ k) p)))
```

### Multiplication by a nonzero number reflects divisibility

```agda
reflects-div-mul-ℤ :
  (k x y : ℤ) → is-nonzero-ℤ k → div-ℤ (mul-ℤ k x) (mul-ℤ k y) → div-ℤ x y
pr1 (reflects-div-mul-ℤ k x y H (pair q p)) = q
pr2 (reflects-div-mul-ℤ k x y H (pair q p)) =
  is-injective-mul-ℤ k H
    ( ( inv (associative-mul-ℤ k q x)) ∙
      ( ( ap (mul-ℤ' x) (commutative-mul-ℤ k q)) ∙
        ( ( associative-mul-ℤ q k x) ∙
          ( p))))
```

### If a nonzero number `d` divides `y`, then `dx` divides `y` if and only if `x` divides the quotient `y/d`.

```agda
div-quotient-div-div-ℤ :
  (x y d : ℤ) (H : div-ℤ d y) → is-nonzero-ℤ d →
  div-ℤ (mul-ℤ d x) y → div-ℤ x (quotient-div-ℤ d y H)
div-quotient-div-div-ℤ x y d H f K =
  reflects-div-mul-ℤ d x
    ( quotient-div-ℤ d y H)
    ( f)
    ( tr (div-ℤ (mul-ℤ d x)) (inv (eq-quotient-div-ℤ' d y H)) K)

div-div-quotient-div-ℤ :
  (x y d : ℤ) (H : div-ℤ d y) →
  div-ℤ x (quotient-div-ℤ d y H) → div-ℤ (mul-ℤ d x) y
div-div-quotient-div-ℤ x y d H K =
  tr ( div-ℤ (mul-ℤ d x))
     ( eq-quotient-div-ℤ' d y H)
     ( preserves-div-mul-ℤ d x (quotient-div-ℤ d y H) K)
```

### Comparison of divisibility on ℕ and on ℤ

```agda
div-int-div-ℕ :
  {x y : ℕ} → div-ℕ x y → div-ℤ (int-ℕ x) (int-ℕ y)
pr1 (div-int-div-ℕ {x} {y} (pair d p)) = int-ℕ d
pr2 (div-int-div-ℕ {x} {y} (pair d p)) = mul-int-ℕ d x ∙ ap int-ℕ p

div-div-int-ℕ :
  {x y : ℕ} → div-ℤ (int-ℕ x) (int-ℕ y) → div-ℕ x y
div-div-int-ℕ {zero-ℕ} {y} (pair d p) =
  div-eq-ℕ zero-ℕ y
    ( inv (is-injective-int-ℕ (is-zero-div-zero-ℤ (int-ℕ y) (pair d p))))
pr1 (div-div-int-ℕ {succ-ℕ x} {y} (pair d p)) = abs-ℤ d
pr2 (div-div-int-ℕ {succ-ℕ x} {y} (pair d p)) =
  is-injective-int-ℕ
    ( ( inv (mul-int-ℕ (abs-ℤ d) (succ-ℕ x))) ∙
      ( ( ap
          ( mul-ℤ' (inr (inr x)))
          { int-abs-ℤ d}
          { d}
          ( int-abs-is-nonnegative-ℤ d
            ( is-nonnegative-left-factor-mul-ℤ
              { d}
              { inr (inr x)}
              ( is-nonnegative-eq-ℤ (inv p) (is-nonnegative-int-ℕ y))
              ( star)))) ∙
        ( p)))
```

### We introduce units

```agda
is-unit-ℤ : ℤ → UU lzero
is-unit-ℤ x = div-ℤ x one-ℤ

unit-ℤ : UU lzero
unit-ℤ = Σ ℤ is-unit-ℤ

int-unit-ℤ : unit-ℤ → ℤ
int-unit-ℤ = pr1

is-unit-int-unit-ℤ : (x : unit-ℤ) → is-unit-ℤ (int-unit-ℤ x)
is-unit-int-unit-ℤ = pr2

div-is-unit-ℤ :
  (x y : ℤ) → is-unit-ℤ x → div-ℤ x y
pr1 (div-is-unit-ℤ x y (pair d p)) = mul-ℤ y d
pr2 (div-is-unit-ℤ x y (pair d p)) =
  associative-mul-ℤ y d x ∙ (ap (mul-ℤ y) p ∙ right-unit-law-mul-ℤ y)
```

### An integer is a unit if and only if it is `1` or `-1`.

```agda
is-one-or-neg-one-ℤ : ℤ → UU lzero
is-one-or-neg-one-ℤ x = (is-one-ℤ x) + (is-neg-one-ℤ x)

is-unit-one-ℤ : is-unit-ℤ one-ℤ
is-unit-one-ℤ = refl-div-ℤ one-ℤ

one-unit-ℤ : unit-ℤ
pr1 one-unit-ℤ = one-ℤ
pr2 one-unit-ℤ = is-unit-one-ℤ

is-unit-is-one-ℤ :
  (x : ℤ) → is-one-ℤ x → is-unit-ℤ x
is-unit-is-one-ℤ .one-ℤ refl = is-unit-one-ℤ

is-unit-neg-one-ℤ : is-unit-ℤ neg-one-ℤ
pr1 is-unit-neg-one-ℤ = neg-one-ℤ
pr2 is-unit-neg-one-ℤ = refl

neg-one-unit-ℤ : unit-ℤ
pr1 neg-one-unit-ℤ = neg-one-ℤ
pr2 neg-one-unit-ℤ = is-unit-neg-one-ℤ

is-unit-is-neg-one-ℤ :
  (x : ℤ) → is-neg-one-ℤ x → is-unit-ℤ x
is-unit-is-neg-one-ℤ .neg-one-ℤ refl = is-unit-neg-one-ℤ

is-unit-is-one-or-neg-one-ℤ :
  (x : ℤ) → is-one-or-neg-one-ℤ x → is-unit-ℤ x
is-unit-is-one-or-neg-one-ℤ x (inl p) = is-unit-is-one-ℤ x p
is-unit-is-one-or-neg-one-ℤ x (inr p) = is-unit-is-neg-one-ℤ x p

is-one-or-neg-one-is-unit-ℤ :
  (x : ℤ) → is-unit-ℤ x → is-one-or-neg-one-ℤ x
is-one-or-neg-one-is-unit-ℤ (inl zero-ℕ) (pair d p) = inr refl
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inl zero-ℕ) p) =
  ex-falso (Eq-eq-ℤ (inv p ∙ compute-mul-ℤ neg-one-ℤ (inl (succ-ℕ x))))
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inl (succ-ℕ d)) p) =
  ex-falso (Eq-eq-ℤ (inv p ∙ compute-mul-ℤ (inl (succ-ℕ d)) (inl (succ-ℕ x))))
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inr (inl star)) p) =
  ex-falso (Eq-eq-ℤ (inv p ∙ compute-mul-ℤ zero-ℤ (inl (succ-ℕ x))))
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inr (inr zero-ℕ)) p) =
  ex-falso (Eq-eq-ℤ (inv p ∙ compute-mul-ℤ one-ℤ (inl (succ-ℕ x))))
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inr (inr (succ-ℕ d))) p) =
  ex-falso
    ( Eq-eq-ℤ (inv p ∙ compute-mul-ℤ (inr (inr (succ-ℕ d))) (inl (succ-ℕ x))))
is-one-or-neg-one-is-unit-ℤ (inr (inl star)) (pair d p) =
  ex-falso (Eq-eq-ℤ (inv (right-zero-law-mul-ℤ d) ∙ p))
is-one-or-neg-one-is-unit-ℤ (inr (inr zero-ℕ)) (pair d p) = inl refl
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (pair (inl zero-ℕ) p) =
  ex-falso (Eq-eq-ℤ (inv p ∙ compute-mul-ℤ neg-one-ℤ (inr (inr (succ-ℕ x)))))
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (pair (inl (succ-ℕ d)) p) =
  ex-falso
    ( Eq-eq-ℤ (inv p ∙ compute-mul-ℤ (inl (succ-ℕ d)) (inr (inr (succ-ℕ x)))))
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (pair (inr (inl star)) p) =
  ex-falso (Eq-eq-ℤ (inv p ∙ compute-mul-ℤ zero-ℤ (inr (inr (succ-ℕ x)))))
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (pair (inr (inr zero-ℕ)) p) =
  ex-falso (Eq-eq-ℤ (inv p ∙ compute-mul-ℤ one-ℤ (inr (inr (succ-ℕ x)))))
is-one-or-neg-one-is-unit-ℤ
  (inr (inr (succ-ℕ x))) (pair (inr (inr (succ-ℕ d))) p) =
  ex-falso
    ( Eq-eq-ℤ
      ( inv p ∙ compute-mul-ℤ (inr (inr (succ-ℕ d))) (inr (inr (succ-ℕ x)))))
```

### Units are idempotent

```agda
idempotent-is-unit-ℤ : {x : ℤ} → is-unit-ℤ x → mul-ℤ x x ＝ one-ℤ
idempotent-is-unit-ℤ {x} H =
  f (is-one-or-neg-one-is-unit-ℤ x H)
  where
  f : is-one-or-neg-one-ℤ x → mul-ℤ x x ＝ one-ℤ
  f (inl refl) = refl
  f (inr refl) = refl

abstract
  is-one-is-unit-int-ℕ : (x : ℕ) → is-unit-ℤ (int-ℕ x) → is-one-ℕ x
  is-one-is-unit-int-ℕ x H with is-one-or-neg-one-is-unit-ℤ (int-ℕ x) H
  ... | inl p = is-injective-int-ℕ p
  ... | inr p = ex-falso (tr is-nonnegative-ℤ p (is-nonnegative-int-ℕ x))
```

### The product `xy` is a unit if and only if both `x` and `y` are units

```agda
is-unit-mul-ℤ :
  (x y : ℤ) → is-unit-ℤ x → is-unit-ℤ y → is-unit-ℤ (mul-ℤ x y)
pr1 (is-unit-mul-ℤ x y (pair d p) (pair e q)) = mul-ℤ e d
pr2 (is-unit-mul-ℤ x y (pair d p) (pair e q)) =
  ( associative-mul-ℤ e d (mul-ℤ x y)) ∙
    ( ( ap
        ( mul-ℤ e)
        ( ( inv (associative-mul-ℤ d x y)) ∙
          ( ap (mul-ℤ' y) p))) ∙
      ( q))

mul-unit-ℤ : unit-ℤ → unit-ℤ → unit-ℤ
pr1 (mul-unit-ℤ (pair x H) (pair y K)) = mul-ℤ x y
pr2 (mul-unit-ℤ (pair x H) (pair y K)) = is-unit-mul-ℤ x y H K

is-unit-left-factor-mul-ℤ :
  (x y : ℤ) → is-unit-ℤ (mul-ℤ x y) → is-unit-ℤ x
pr1 (is-unit-left-factor-mul-ℤ x y (pair d p)) = mul-ℤ d y
pr2 (is-unit-left-factor-mul-ℤ x y (pair d p)) =
  associative-mul-ℤ d y x ∙ (ap (mul-ℤ d) (commutative-mul-ℤ y x) ∙ p)

is-unit-right-factor-ℤ :
  (x y : ℤ) → is-unit-ℤ (mul-ℤ x y) → is-unit-ℤ y
is-unit-right-factor-ℤ x y (pair d p) =
  is-unit-left-factor-mul-ℤ y x
    ( pair d (ap (mul-ℤ d) (commutative-mul-ℤ y x) ∙ p))
```

### We introduce the equivalence relation `ux = y`, where `u` is a unit

```
{- The relation presim-unit-ℤ would be an equivalence relation, except it is not
   valued in the propositions. Indeed presim-unit-ℤ zero-ℤ zero-ℤ is not a
   proposition. -}
presim-unit-ℤ : ℤ → ℤ → UU lzero
presim-unit-ℤ x y = Σ unit-ℤ (λ u → mul-ℤ (pr1 u) x ＝ y)

{- We could define sim-unit-ℤ x y to be the propositional truncation of
   presim-unit-ℤ, but that's a waste because presim-unit-ℤ x y is only not a
   proposition when both x and y are zero. -}
sim-unit-ℤ : ℤ → ℤ → UU lzero
sim-unit-ℤ x y = ¬ (is-zero-ℤ x × is-zero-ℤ y) → presim-unit-ℤ x y
```

### The relations `presim-unit-ℤ` and `sim-unit-ℤ` are logically equivalent

```agda
sim-unit-presim-unit-ℤ :
  {x y : ℤ} → presim-unit-ℤ x y → sim-unit-ℤ x y
sim-unit-presim-unit-ℤ {x} {y} H f = H

presim-unit-sim-unit-ℤ :
  {x y : ℤ} → sim-unit-ℤ x y → presim-unit-ℤ x y
presim-unit-sim-unit-ℤ {inl x} {inl y} H = H (λ t → Eq-eq-ℤ (pr1 t))
presim-unit-sim-unit-ℤ {inl x} {inr y} H = H (λ t → Eq-eq-ℤ (pr1 t))
presim-unit-sim-unit-ℤ {inr x} {inl y} H = H (λ t → Eq-eq-ℤ (pr2 t))
pr1 (presim-unit-sim-unit-ℤ {inr (inl star)} {inr (inl star)} H) = one-unit-ℤ
pr2 (presim-unit-sim-unit-ℤ {inr (inl star)} {inr (inl star)} H) = refl
presim-unit-sim-unit-ℤ {inr (inl star)} {inr (inr y)} H =
  H (λ t → Eq-eq-ℤ (pr2 t))
presim-unit-sim-unit-ℤ {inr (inr x)} {inr (inl star)} H =
  H (λ t → Eq-eq-ℤ (pr1 t))
presim-unit-sim-unit-ℤ {inr (inr x)} {inr (inr y)} H =
  H (λ t → Eq-eq-ℤ (pr1 t))
```

### The relations `presim-unit-ℤ` and `sim-unit-ℤ` relate `zero-ℤ` only to itself

```agda
is-nonzero-presim-unit-ℤ :
  {x y : ℤ} → presim-unit-ℤ x y → is-nonzero-ℤ x → is-nonzero-ℤ y
is-nonzero-presim-unit-ℤ {x} {y} (pair (pair v (pair u α)) β) f p =
  Eq-eq-ℤ (ap (mul-ℤ' u) (inv q) ∙ (commutative-mul-ℤ v u ∙ α))
  where
  q : is-zero-ℤ v
  q = is-injective-mul-ℤ' x f {v} {zero-ℤ} (β ∙ p)

is-nonzero-sim-unit-ℤ :
  {x y : ℤ} → sim-unit-ℤ x y → is-nonzero-ℤ x → is-nonzero-ℤ y
is-nonzero-sim-unit-ℤ H f =
  is-nonzero-presim-unit-ℤ (H (f ∘ pr1)) f

is-zero-sim-unit-ℤ :
  {x y : ℤ} → sim-unit-ℤ x y → is-zero-ℤ x → is-zero-ℤ y
is-zero-sim-unit-ℤ {x} {y} H p =
  dn-elim-is-decidable
    ( has-decidable-equality-ℤ y zero-ℤ)
    ( λ g → g (inv (β g) ∙ (ap (mul-ℤ (u g)) p ∙ right-zero-law-mul-ℤ (u g))))
  where
  K : is-nonzero-ℤ y → presim-unit-ℤ x y
  K g = H (λ {(pair u v) → g v})
  u : is-nonzero-ℤ y → ℤ
  u g = pr1 (pr1 (K g))
  v : is-nonzero-ℤ y → ℤ
  v g = pr1 (pr2 (pr1 (K g)))
  β : (g : is-nonzero-ℤ y) → mul-ℤ (u g) x ＝ y
  β g = pr2 (K g)
```

### The relations `presim-unit-ℤ` and `sim-unit-ℤ` are equivalence relations

```agda
refl-presim-unit-ℤ : (x : ℤ) → presim-unit-ℤ x x
pr1 (refl-presim-unit-ℤ x) = one-unit-ℤ
pr2 (refl-presim-unit-ℤ x) = left-unit-law-mul-ℤ x

refl-sim-unit-ℤ : (x : ℤ) → sim-unit-ℤ x x
refl-sim-unit-ℤ x f = refl-presim-unit-ℤ x

presim-unit-eq-ℤ : {x y : ℤ} → x ＝ y → presim-unit-ℤ x y
presim-unit-eq-ℤ {x} refl = refl-presim-unit-ℤ x

sim-unit-eq-ℤ : {x y : ℤ} → x ＝ y → sim-unit-ℤ x y
sim-unit-eq-ℤ {x} refl = refl-sim-unit-ℤ x

symm-presim-unit-ℤ : {x y : ℤ} → presim-unit-ℤ x y → presim-unit-ℤ y x
symm-presim-unit-ℤ {x} {y} (pair (pair u H) p) =
  f (is-one-or-neg-one-is-unit-ℤ u H)
  where
  f : is-one-or-neg-one-ℤ u → presim-unit-ℤ y x
  pr1 (f (inl refl)) = one-unit-ℤ
  pr2 (f (inl refl)) = inv p
  pr1 (f (inr refl)) = neg-one-unit-ℤ
  pr2 (f (inr refl)) = inv (inv (neg-neg-ℤ x) ∙ ap (mul-ℤ neg-one-ℤ) p)

symm-sim-unit-ℤ : {x y : ℤ} → sim-unit-ℤ x y → sim-unit-ℤ y x
symm-sim-unit-ℤ {x} {y} H f =
  symm-presim-unit-ℤ (H (λ p → f (pair (pr2 p) (pr1 p))))

is-nonzero-sim-unit-ℤ' :
  {x y : ℤ} → sim-unit-ℤ x y → is-nonzero-ℤ y → is-nonzero-ℤ x
is-nonzero-sim-unit-ℤ' H = is-nonzero-sim-unit-ℤ (symm-sim-unit-ℤ H)

is-zero-sim-unit-ℤ' :
  {x y : ℤ} → sim-unit-ℤ x y → is-zero-ℤ y → is-zero-ℤ x
is-zero-sim-unit-ℤ' H = is-zero-sim-unit-ℤ (symm-sim-unit-ℤ H)

trans-presim-unit-ℤ :
  (x y z : ℤ) → presim-unit-ℤ x y → presim-unit-ℤ y z → presim-unit-ℤ x z
trans-presim-unit-ℤ x y z (pair (pair u H) p) (pair (pair v K) q) =
  f (is-one-or-neg-one-is-unit-ℤ u H) (is-one-or-neg-one-is-unit-ℤ v K)
  where
  f : is-one-or-neg-one-ℤ u → is-one-or-neg-one-ℤ v → presim-unit-ℤ x z
  pr1 (f (inl refl) (inl refl)) = one-unit-ℤ
  pr2 (f (inl refl) (inl refl)) = p ∙ q
  pr1 (f (inl refl) (inr refl)) = neg-one-unit-ℤ
  pr2 (f (inl refl) (inr refl)) = ap neg-ℤ p ∙ q
  pr1 (f (inr refl) (inl refl)) = neg-one-unit-ℤ
  pr2 (f (inr refl) (inl refl)) = p ∙ q
  pr1 (f (inr refl) (inr refl)) = one-unit-ℤ
  pr2 (f (inr refl) (inr refl)) = inv (neg-neg-ℤ x) ∙ (ap neg-ℤ p ∙ q)

trans-sim-unit-ℤ :
  (x y z : ℤ) → sim-unit-ℤ x y → sim-unit-ℤ y z → sim-unit-ℤ x z
trans-sim-unit-ℤ x y z H K f =
  trans-presim-unit-ℤ x y z
    ( H (λ {(pair p q) → f (pair p (is-zero-sim-unit-ℤ K q))}))
    ( K (λ {(pair p q) → f (pair (is-zero-sim-unit-ℤ' H p) q)}))
```

### We show that `sim-unit-ℤ x y` holds if and only if `x|y` and `y|x`

```agda
antisymmetric-div-ℤ :
  (x y : ℤ) → div-ℤ x y → div-ℤ y x → sim-unit-ℤ x y
antisymmetric-div-ℤ x y (pair d p) (pair e q) H =
  f (is-decidable-is-zero-ℤ x)
  where
  f : is-decidable (is-zero-ℤ x) → presim-unit-ℤ x y
  f (inl refl) = presim-unit-eq-ℤ (inv (right-zero-law-mul-ℤ d) ∙ p)
  pr1 (pr1 (f (inr g))) = d
  pr1 (pr2 (pr1 (f (inr g)))) = e
  pr2 (pr2 (pr1 (f (inr g)))) =
    is-injective-mul-ℤ x g
      ( ( commutative-mul-ℤ x (mul-ℤ e d)) ∙
        ( ( associative-mul-ℤ e d x) ∙
          ( ( ap (mul-ℤ e) p) ∙
            ( q ∙ inv (right-unit-law-mul-ℤ x)))))
  pr2 (f (inr g)) = p
```

### We show that `sim-unit-ℤ |x| x` holds

```agda
sim-unit-abs-ℤ : (x : ℤ) → sim-unit-ℤ (int-abs-ℤ x) x
pr1 (sim-unit-abs-ℤ (inl x) f) = neg-one-unit-ℤ
pr2 (sim-unit-abs-ℤ (inl x) f) = refl
sim-unit-abs-ℤ (inr (inl star)) = refl-sim-unit-ℤ zero-ℤ
sim-unit-abs-ℤ (inr (inr x)) = refl-sim-unit-ℤ (inr (inr x))

div-presim-unit-ℤ :
  {x y x' y' : ℤ} → presim-unit-ℤ x x' → presim-unit-ℤ y y' →
  div-ℤ x y → div-ℤ x' y'
pr1 (div-presim-unit-ℤ {x} {y} {x'} {y'} (pair u q) (pair v r) (pair d p)) =
  mul-ℤ (mul-ℤ (int-unit-ℤ v) d) (int-unit-ℤ u)
pr2 (div-presim-unit-ℤ {x} {y} {x'} {y'} (pair u q) (pair v r) (pair d p)) =
  ( ap (mul-ℤ (mul-ℤ (mul-ℤ (int-unit-ℤ v) d) (int-unit-ℤ u))) (inv q)) ∙
  ( ( associative-mul-ℤ
      ( mul-ℤ (int-unit-ℤ v) d)
      ( int-unit-ℤ u)
      ( mul-ℤ (int-unit-ℤ u) x)) ∙
    ( ( ap
        ( mul-ℤ (mul-ℤ (int-unit-ℤ v) d))
        ( ( inv (associative-mul-ℤ (int-unit-ℤ u) (int-unit-ℤ u) x)) ∙
          ( ap (mul-ℤ' x) (idempotent-is-unit-ℤ (is-unit-int-unit-ℤ u))))) ∙
      ( ( associative-mul-ℤ (int-unit-ℤ v) d x) ∙
        ( ( ap (mul-ℤ (int-unit-ℤ v)) p) ∙
          ( r)))))

div-sim-unit-ℤ :
  {x y x' y' : ℤ} → sim-unit-ℤ x x' → sim-unit-ℤ y y' →
  div-ℤ x y → div-ℤ x' y'
div-sim-unit-ℤ {x} {y} {x'} {y'} H K =
  div-presim-unit-ℤ (presim-unit-sim-unit-ℤ H) (presim-unit-sim-unit-ℤ K)

div-int-abs-div-ℤ :
  {x y : ℤ} → div-ℤ x y → div-ℤ (int-abs-ℤ x) y
div-int-abs-div-ℤ {x} {y} =
  div-sim-unit-ℤ (symm-sim-unit-ℤ (sim-unit-abs-ℤ x)) (refl-sim-unit-ℤ y)

div-div-int-abs-ℤ :
  {x y : ℤ} → div-ℤ (int-abs-ℤ x) y → div-ℤ x y
div-div-int-abs-ℤ {x} {y} =
  div-sim-unit-ℤ (sim-unit-abs-ℤ x) (refl-sim-unit-ℤ y)
```

### If we have that `sim-unit-ℤ x y`, then they must differ only by sign

```agda
is-plus-or-minus-sim-unit-ℤ : {x y : ℤ} → sim-unit-ℤ x y → is-plus-or-minus-ℤ x y
is-plus-or-minus-sim-unit-ℤ {x} {y} H with ( is-decidable-is-zero-ℤ x)
is-plus-or-minus-sim-unit-ℤ {x} {y} H | inl z = inl (z ∙ inv (is-zero-sim-unit-ℤ H z))
is-plus-or-minus-sim-unit-ℤ {x} {y} H | inr nz with ( is-one-or-neg-one-is-unit-ℤ
        (int-unit-ℤ (pr1 (H (λ - → nz (pr1 -)))))
        (is-unit-int-unit-ℤ (pr1 (H (λ - → nz (pr1 -))))) )
is-plus-or-minus-sim-unit-ℤ {x} {y} H | inr nz | inl pos = inl (equational-reasoning
         x  ＝ mul-ℤ one-ℤ x                             by (inv (left-unit-law-mul-ℤ x))
            ＝ mul-ℤ (int-unit-ℤ (pr1 (H (λ - → nz (pr1 -))))) x by inv (ap (λ - → mul-ℤ - x) pos)
            ＝ y                                         by pr2 (H (λ - → nz (pr1 -))))
is-plus-or-minus-sim-unit-ℤ {x} {y} H | inr nz | inr neg = inr (equational-reasoning
         neg-ℤ x
         ＝ mul-ℤ (int-unit-ℤ (pr1 (H (λ - → nz (pr1 -))))) x by tr (λ - → neg-ℤ x ＝ mul-ℤ - x)
                                                           (inv neg)
                                                           (left-neg-unit-law-mul-ℤ x)
         ＝ y                                         by pr2 (H (λ - → nz (pr1 -))))
```

### If we have that `sim-unit-ℤ x y` and both `x` and `y` have the same sign,
then they are the same

```agda
eq-sim-unit-is-nonnegative-ℤ :
  {a b : ℤ} → is-nonnegative-ℤ a → is-nonnegative-ℤ b → sim-unit-ℤ a b → a ＝ b
eq-sim-unit-is-nonnegative-ℤ {a} {b} H H' K with
  ( is-plus-or-minus-sim-unit-ℤ K )
eq-sim-unit-is-nonnegative-ℤ {a} {b} H H' K | inl pos = pos
eq-sim-unit-is-nonnegative-ℤ {a} {b} H H' K | inr neg with ( is-decidable-is-zero-ℤ a )
eq-sim-unit-is-nonnegative-ℤ {a} {b} H H' K | inr neg | inl z =
  equational-reasoning
    a ＝ zero-ℤ   by z
      ＝ neg-ℤ a  by inv (ap neg-ℤ z)
      ＝ b        by neg
eq-sim-unit-is-nonnegative-ℤ {a} {b} H H' K | inr neg | inr nz =
  ex-falso ( nz ( is-zero-is-nonnegative-neg-is-nonnegative-ℤ
   a H (tr is-nonnegative-ℤ (inv neg) H')))
```
