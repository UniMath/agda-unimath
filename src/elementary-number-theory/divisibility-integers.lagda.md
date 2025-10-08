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
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.nonpositive-integers
open import elementary-number-theory.nonzero-integers
open import elementary-number-theory.positive-and-negative-integers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

An integer `m` is said to **divide** an integer `n` if there exists an integer
`k` equipped with an identification `km ＝ n`. Using the
[Curry–Howard interpretation](https://en.wikipedia.org/wiki/Curry–Howard_correspondence)
of logic into type theory, we express divisibility as follows:

```text
  div-ℤ m n := Σ (k : ℤ), k *ℤ m ＝ n.
```

If `n` is a nonzero integer, then `div-ℤ m n` is always a proposition in the
sense that the type `div-ℤ m n` contains at most one element.

We also introduce **unit integers**, which are integers that divide the integer
`1`, and an equivalence relation `sim-unit-ℤ` on the integers in which two
integers `x` and `y` are equivalent if there exists a unit integer `u` such that
`ux ＝ y`. These two concepts help establish further properties of the
divisibility relation on the integers.

## Definitions

```agda
div-ℤ : ℤ → ℤ → UU lzero
div-ℤ d x = Σ ℤ (λ k → k *ℤ d ＝ x)

quotient-div-ℤ : (x y : ℤ) → div-ℤ x y → ℤ
quotient-div-ℤ x y H = pr1 H
```

### Unit integers

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
pr1 (div-is-unit-ℤ x y (pair d p)) = y *ℤ d
pr2 (div-is-unit-ℤ x y (pair d p)) =
  associative-mul-ℤ y d x ∙ (ap (y *ℤ_) p ∙ right-unit-law-mul-ℤ y)
```

### The equivalence relation `sim-unit-ℤ`

We define the equivalence relation `sim-unit-ℤ` in such a way that
`sim-unit-ℤ x y` is always a proposition.

```agda
presim-unit-ℤ : ℤ → ℤ → UU lzero
presim-unit-ℤ x y = Σ unit-ℤ (λ u → (pr1 u) *ℤ x ＝ y)

sim-unit-ℤ : ℤ → ℤ → UU lzero
sim-unit-ℤ x y = ¬ (is-zero-ℤ x × is-zero-ℤ y) → presim-unit-ℤ x y
```

## Properties

### If `d` divides `x`, the quotient times `d` equals `x`

```agda
eq-quotient-div-ℤ :
  (x y : ℤ) (H : div-ℤ x y) → (quotient-div-ℤ x y H) *ℤ x ＝ y
eq-quotient-div-ℤ x y H = pr2 H

eq-quotient-div-ℤ' :
  (x y : ℤ) (H : div-ℤ x y) → x *ℤ (quotient-div-ℤ x y H) ＝ y
eq-quotient-div-ℤ' x y H =
  commutative-mul-ℤ x (quotient-div-ℤ x y H) ∙ eq-quotient-div-ℤ x y H
```

### If `d` divides `x`, the quotient also divides `x`

```agda
div-quotient-div-ℤ :
  (d x : ℤ) (H : div-ℤ d x) → div-ℤ (quotient-div-ℤ d x H) x
pr1 (div-quotient-div-ℤ d x (u , p)) = d
pr2 (div-quotient-div-ℤ d x (u , p)) = commutative-mul-ℤ d u ∙ p
```

### Concatenating equalities and divisibility

```agda
concatenate-eq-div-ℤ :
  {x y z : ℤ} → x ＝ y → div-ℤ y z → div-ℤ x z
concatenate-eq-div-ℤ refl p = p

concatenate-div-eq-ℤ :
  {x y z : ℤ} → div-ℤ x y → y ＝ z → div-ℤ x z
concatenate-div-eq-ℤ p refl = p

concatenate-eq-div-eq-ℤ :
  {x y z w : ℤ} → x ＝ y → div-ℤ y z → z ＝ w → div-ℤ x w
concatenate-eq-div-eq-ℤ refl p refl = p
```

### Divisibility by a nonzero integer is a property

```agda
abstract
  is-prop-div-ℤ : (d x : ℤ) → is-nonzero-ℤ d → is-prop (div-ℤ d x)
  is-prop-div-ℤ d x f = is-prop-map-is-emb (is-emb-right-mul-ℤ d f) x
```

### The divisibility relation is a preorder

Note that the divisibility relation on the integers is not antisymmetric.

```agda
refl-div-ℤ : is-reflexive div-ℤ
pr1 (refl-div-ℤ x) = one-ℤ
pr2 (refl-div-ℤ x) = left-unit-law-mul-ℤ x

transitive-div-ℤ : is-transitive div-ℤ
pr1 (transitive-div-ℤ x y z (pair e q) (pair d p)) = e *ℤ d
pr2 (transitive-div-ℤ x y z (pair e q) (pair d p)) =
  ( associative-mul-ℤ e d x) ∙
    ( ( ap (e *ℤ_) p) ∙
      ( q))
```

### Every integer is divisible by `1`

```agda
div-one-ℤ : (x : ℤ) → div-ℤ one-ℤ x
pr1 (div-one-ℤ x) = x
pr2 (div-one-ℤ x) = right-unit-law-mul-ℤ x
```

### Every integer divides `0`

```agda
div-zero-ℤ : (x : ℤ) → div-ℤ x zero-ℤ
pr1 (div-zero-ℤ x) = zero-ℤ
pr2 (div-zero-ℤ x) = left-zero-law-mul-ℤ x
```

### Every integer that is divisible by `0` is `0`

```agda
abstract
  is-zero-div-zero-ℤ :
    (x : ℤ) → div-ℤ zero-ℤ x → is-zero-ℤ x
  is-zero-div-zero-ℤ x (pair d p) = inv p ∙ right-zero-law-mul-ℤ d
```

### The quotient of `x` by one is `x`

```agda
abstract
  eq-quotient-div-is-one-ℤ :
    (k x : ℤ) → is-one-ℤ k → (H : div-ℤ k x) → quotient-div-ℤ k x H ＝ x
  eq-quotient-div-is-one-ℤ .one-ℤ x refl H =
    ap
      ( quotient-div-ℤ one-ℤ x)
      ( inv
        ( eq-is-prop'
          ( is-prop-div-ℤ one-ℤ x (λ ()))
          ( div-one-ℤ x)
          ( H)))
```

### If `k` divides `x` and `k` is `0` then `x` is `0`

```agda
abstract
  is-zero-is-zero-div-ℤ : (x k : ℤ) → div-ℤ k x → is-zero-ℤ k → is-zero-ℤ x
  is-zero-is-zero-div-ℤ x .zero-ℤ k-div-x refl = is-zero-div-zero-ℤ x k-div-x
```

### If `x` divides both `y` and `z`, then it divides `y + z`

```agda
div-add-ℤ : (x y z : ℤ) → div-ℤ x y → div-ℤ x z → div-ℤ x (y +ℤ z)
pr1 (div-add-ℤ x y z (pair d p) (pair e q)) = d +ℤ e
pr2 (div-add-ℤ x y z (pair d p) (pair e q)) =
  ( right-distributive-mul-add-ℤ d e x) ∙
  ( ap-add-ℤ p q)
```

### If `x` divides `y` then `x` divides any multiple of `y`

```agda
div-mul-ℤ :
  (k x y : ℤ) → div-ℤ x y → div-ℤ x (k *ℤ y)
div-mul-ℤ k x y = transitive-div-ℤ x y (k *ℤ y) (k , refl)
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
    (neg-ℤ d) *ℤ (neg-ℤ x)
    ＝ neg-ℤ (d *ℤ (neg-ℤ x))
      by left-negative-law-mul-ℤ d (neg-ℤ x)
    ＝ neg-ℤ (neg-ℤ (d *ℤ x))
      by ap neg-ℤ (right-negative-law-mul-ℤ d x)
    ＝ (d *ℤ x)
      by neg-neg-ℤ (d *ℤ x)
    ＝ y
      by p
```

### Multiplication preserves divisibility

```agda
preserves-div-mul-ℤ :
  (k x y : ℤ) → div-ℤ x y → div-ℤ (k *ℤ x) (k *ℤ y)
pr1 (preserves-div-mul-ℤ k x y (pair q p)) = q
pr2 (preserves-div-mul-ℤ k x y (pair q p)) =
  ( inv (associative-mul-ℤ q k x)) ∙
  ( ap (_*ℤ x) (commutative-mul-ℤ q k)) ∙
  ( associative-mul-ℤ k q x) ∙
  ( ap (k *ℤ_) p)
```

### Multiplication by a nonzero number reflects divisibility

```agda
abstract
  reflects-div-mul-ℤ :
    (k x y : ℤ) → is-nonzero-ℤ k → div-ℤ (k *ℤ x) (k *ℤ y) → div-ℤ x y
  pr1 (reflects-div-mul-ℤ k x y H (pair q p)) = q
  pr2 (reflects-div-mul-ℤ k x y H (pair q p)) =
    is-injective-left-mul-ℤ k H
      ( ( inv (associative-mul-ℤ k q x)) ∙
        ( ap (_*ℤ x) (commutative-mul-ℤ k q)) ∙
        ( associative-mul-ℤ q k x) ∙
        ( p))
```

### If a nonzero number `d` divides `y`, then `dx` divides `y` if and only if `x` divides the quotient `y/d`

```agda
div-quotient-div-div-ℤ :
  (x y d : ℤ) (H : div-ℤ d y) → is-nonzero-ℤ d →
  div-ℤ (d *ℤ x) y → div-ℤ x (quotient-div-ℤ d y H)
div-quotient-div-div-ℤ x y d H f K =
  reflects-div-mul-ℤ d x
    ( quotient-div-ℤ d y H)
    ( f)
    ( tr (div-ℤ (d *ℤ x)) (inv (eq-quotient-div-ℤ' d y H)) K)

div-div-quotient-div-ℤ :
  (x y d : ℤ) (H : div-ℤ d y) →
  div-ℤ x (quotient-div-ℤ d y H) → div-ℤ (d *ℤ x) y
div-div-quotient-div-ℤ x y d H K =
  tr
    ( div-ℤ (d *ℤ x))
    ( eq-quotient-div-ℤ' d y H)
    ( preserves-div-mul-ℤ d x (quotient-div-ℤ d y H) K)
```

### The canonical embedding of natural numbers preserves and reflects divisibility

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
          ( _*ℤ (inr (inr x)))
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

### An integer is a unit if and only if it is `1` or `-1`

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

abstract
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
  is-one-or-neg-one-is-unit-ℤ
    (inr (inr (succ-ℕ x))) (pair (inr (inr zero-ℕ)) p) =
    ex-falso (Eq-eq-ℤ (inv p ∙ compute-mul-ℤ one-ℤ (inr (inr (succ-ℕ x)))))
  is-one-or-neg-one-is-unit-ℤ
    (inr (inr (succ-ℕ x))) (pair (inr (inr (succ-ℕ d))) p) =
    ex-falso
      ( Eq-eq-ℤ
        ( inv p ∙ compute-mul-ℤ (inr (inr (succ-ℕ d))) (inr (inr (succ-ℕ x)))))
```

### Units are idempotent

```agda
abstract
  idempotent-is-unit-ℤ : {x : ℤ} → is-unit-ℤ x → x *ℤ x ＝ one-ℤ
  idempotent-is-unit-ℤ {x} H =
    f (is-one-or-neg-one-is-unit-ℤ x H)
    where
    f : is-one-or-neg-one-ℤ x → x *ℤ x ＝ one-ℤ
    f (inl refl) = refl
    f (inr refl) = refl

  is-one-is-unit-int-ℕ : (x : ℕ) → is-unit-ℤ (int-ℕ x) → is-one-ℕ x
  is-one-is-unit-int-ℕ x H with is-one-or-neg-one-is-unit-ℤ (int-ℕ x) H
  ... | inl p = is-injective-int-ℕ p
  ... | inr p = ex-falso (tr is-nonnegative-ℤ p (is-nonnegative-int-ℕ x))
```

### The product `xy` is a unit if and only if both `x` and `y` are units

```agda
abstract
  is-unit-mul-ℤ :
    (x y : ℤ) → is-unit-ℤ x → is-unit-ℤ y → is-unit-ℤ (x *ℤ y)
  pr1 (is-unit-mul-ℤ x y (pair d p) (pair e q)) = e *ℤ d
  pr2 (is-unit-mul-ℤ x y (pair d p) (pair e q)) =
    ( associative-mul-ℤ e d (x *ℤ y)) ∙
      ( ( ap
          ( e *ℤ_)
          ( ( inv (associative-mul-ℤ d x y)) ∙
            ( ap (_*ℤ y) p))) ∙
        ( q))

mul-unit-ℤ : unit-ℤ → unit-ℤ → unit-ℤ
pr1 (mul-unit-ℤ (pair x H) (pair y K)) = x *ℤ y
pr2 (mul-unit-ℤ (pair x H) (pair y K)) = is-unit-mul-ℤ x y H K

abstract
  is-unit-left-factor-mul-ℤ :
    (x y : ℤ) → is-unit-ℤ (x *ℤ y) → is-unit-ℤ x
  pr1 (is-unit-left-factor-mul-ℤ x y (pair d p)) = d *ℤ y
  pr2 (is-unit-left-factor-mul-ℤ x y (pair d p)) =
    associative-mul-ℤ d y x ∙ (ap (d *ℤ_) (commutative-mul-ℤ y x) ∙ p)

  is-unit-right-factor-ℤ :
    (x y : ℤ) → is-unit-ℤ (x *ℤ y) → is-unit-ℤ y
  is-unit-right-factor-ℤ x y (pair d p) =
    is-unit-left-factor-mul-ℤ y x
      ( pair d (ap (d *ℤ_) (commutative-mul-ℤ y x) ∙ p))
```

### The relations `presim-unit-ℤ` and `sim-unit-ℤ` are logically equivalent

```agda
abstract
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
abstract
  is-nonzero-presim-unit-ℤ :
    {x y : ℤ} → presim-unit-ℤ x y → is-nonzero-ℤ x → is-nonzero-ℤ y
  is-nonzero-presim-unit-ℤ {x} {y} (pair (pair v (pair u α)) β) f p =
    Eq-eq-ℤ (ap (_*ℤ u) (inv q) ∙ (commutative-mul-ℤ v u ∙ α))
    where
    q : is-zero-ℤ v
    q = is-injective-right-mul-ℤ x f {v} {zero-ℤ} (β ∙ p)

  is-nonzero-sim-unit-ℤ :
    {x y : ℤ} → sim-unit-ℤ x y → is-nonzero-ℤ x → is-nonzero-ℤ y
  is-nonzero-sim-unit-ℤ H f =
    is-nonzero-presim-unit-ℤ (H (f ∘ pr1)) f

  is-zero-sim-unit-ℤ :
    {x y : ℤ} → sim-unit-ℤ x y → is-zero-ℤ x → is-zero-ℤ y
  is-zero-sim-unit-ℤ {x} {y} H p =
    double-negation-elim-is-decidable
      ( has-decidable-equality-ℤ y zero-ℤ)
      ( λ g → g (inv (β g) ∙ (ap ((u g) *ℤ_) p ∙ right-zero-law-mul-ℤ (u g))))
    where
    K : is-nonzero-ℤ y → presim-unit-ℤ x y
    K g = H (λ (u , v) → g v)
    u : is-nonzero-ℤ y → ℤ
    u g = pr1 (pr1 (K g))
    v : is-nonzero-ℤ y → ℤ
    v g = pr1 (pr2 (pr1 (K g)))
    β : (g : is-nonzero-ℤ y) → (u g) *ℤ x ＝ y
    β g = pr2 (K g)
```

### The relations `presim-unit-ℤ` and `sim-unit-ℤ` are equivalence relations

```agda
abstract
  refl-presim-unit-ℤ : is-reflexive presim-unit-ℤ
  pr1 (refl-presim-unit-ℤ x) = one-unit-ℤ
  pr2 (refl-presim-unit-ℤ x) = left-unit-law-mul-ℤ x

  refl-sim-unit-ℤ : is-reflexive sim-unit-ℤ
  refl-sim-unit-ℤ x f = refl-presim-unit-ℤ x

  presim-unit-eq-ℤ : {x y : ℤ} → x ＝ y → presim-unit-ℤ x y
  presim-unit-eq-ℤ {x} refl = refl-presim-unit-ℤ x

  sim-unit-eq-ℤ : {x y : ℤ} → x ＝ y → sim-unit-ℤ x y
  sim-unit-eq-ℤ {x} refl = refl-sim-unit-ℤ x

  symmetric-presim-unit-ℤ : is-symmetric presim-unit-ℤ
  symmetric-presim-unit-ℤ x y (pair (pair u H) p) =
    f (is-one-or-neg-one-is-unit-ℤ u H)
    where
    f : is-one-or-neg-one-ℤ u → presim-unit-ℤ y x
    pr1 (f (inl refl)) = one-unit-ℤ
    pr2 (f (inl refl)) = inv p
    pr1 (f (inr refl)) = neg-one-unit-ℤ
    pr2 (f (inr refl)) = inv (inv (neg-neg-ℤ x) ∙ ap (neg-one-ℤ *ℤ_) p)

  symmetric-sim-unit-ℤ : is-symmetric sim-unit-ℤ
  symmetric-sim-unit-ℤ x y H f =
    symmetric-presim-unit-ℤ x y (H (λ p → f (pair (pr2 p) (pr1 p))))

  is-nonzero-sim-unit-ℤ' :
    {x y : ℤ} → sim-unit-ℤ x y → is-nonzero-ℤ y → is-nonzero-ℤ x
  is-nonzero-sim-unit-ℤ' {x} {y} H =
    is-nonzero-sim-unit-ℤ (symmetric-sim-unit-ℤ x y H)

  is-zero-sim-unit-ℤ' :
    {x y : ℤ} → sim-unit-ℤ x y → is-zero-ℤ y → is-zero-ℤ x
  is-zero-sim-unit-ℤ' {x} {y} H =
    is-zero-sim-unit-ℤ (symmetric-sim-unit-ℤ x y H)

  transitive-presim-unit-ℤ : is-transitive presim-unit-ℤ
  transitive-presim-unit-ℤ x y z (pair (pair v K) q) (pair (pair u H) p) =
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

  transitive-sim-unit-ℤ : is-transitive sim-unit-ℤ
  transitive-sim-unit-ℤ x y z K H f =
    transitive-presim-unit-ℤ x y z
      ( K (λ (p , q) → f (is-zero-sim-unit-ℤ' H p , q)))
      ( H (λ (p , q) → f (p , is-zero-sim-unit-ℤ K q)))
```

### `sim-unit-ℤ x y` holds if and only if `x|y` and `y|x`

```agda
abstract
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
      is-injective-left-mul-ℤ x g
        ( ( commutative-mul-ℤ x (e *ℤ d)) ∙
          ( ( associative-mul-ℤ e d x) ∙
            ( ( ap (e *ℤ_) p) ∙
              ( q ∙ inv (right-unit-law-mul-ℤ x)))))
    pr2 (f (inr g)) = p
```

### `sim-unit-ℤ |x| x` holds

```agda
abstract
  sim-unit-abs-ℤ : (x : ℤ) → sim-unit-ℤ (int-abs-ℤ x) x
  pr1 (sim-unit-abs-ℤ (inl x) f) = neg-one-unit-ℤ
  pr2 (sim-unit-abs-ℤ (inl x) f) = refl
  sim-unit-abs-ℤ (inr (inl star)) = refl-sim-unit-ℤ zero-ℤ
  sim-unit-abs-ℤ (inr (inr x)) = refl-sim-unit-ℤ (inr (inr x))

  div-presim-unit-ℤ :
    {x y x' y' : ℤ} → presim-unit-ℤ x x' → presim-unit-ℤ y y' →
    div-ℤ x y → div-ℤ x' y'
  pr1 (div-presim-unit-ℤ {x} {y} {x'} {y'} (pair u q) (pair v r) (pair d p)) =
    ((int-unit-ℤ v) *ℤ d) *ℤ (int-unit-ℤ u)
  pr2 (div-presim-unit-ℤ {x} {y} {x'} {y'} (pair u q) (pair v r) (pair d p)) =
    ( ap ((((int-unit-ℤ v) *ℤ d) *ℤ (int-unit-ℤ u)) *ℤ_) (inv q)) ∙
    ( ( associative-mul-ℤ
        ( (int-unit-ℤ v) *ℤ d)
        ( int-unit-ℤ u)
        ( (int-unit-ℤ u) *ℤ x)) ∙
      ( ( ap
          ( ((int-unit-ℤ v) *ℤ d) *ℤ_)
          ( ( inv (associative-mul-ℤ (int-unit-ℤ u) (int-unit-ℤ u) x)) ∙
            ( ap (_*ℤ x) (idempotent-is-unit-ℤ (is-unit-int-unit-ℤ u))))) ∙
        ( ( associative-mul-ℤ (int-unit-ℤ v) d x) ∙
          ( ( ap ((int-unit-ℤ v) *ℤ_) p) ∙
            ( r)))))

  div-sim-unit-ℤ :
    {x y x' y' : ℤ} → sim-unit-ℤ x x' → sim-unit-ℤ y y' →
    div-ℤ x y → div-ℤ x' y'
  div-sim-unit-ℤ {x} {y} {x'} {y'} H K =
    div-presim-unit-ℤ (presim-unit-sim-unit-ℤ H) (presim-unit-sim-unit-ℤ K)

  div-int-abs-div-ℤ :
    {x y : ℤ} → div-ℤ x y → div-ℤ (int-abs-ℤ x) y
  div-int-abs-div-ℤ {x} {y} =
    div-sim-unit-ℤ
      ( symmetric-sim-unit-ℤ (int-abs-ℤ x) x (sim-unit-abs-ℤ x))
      ( refl-sim-unit-ℤ y)

  div-div-int-abs-ℤ :
    {x y : ℤ} → div-ℤ (int-abs-ℤ x) y → div-ℤ x y
  div-div-int-abs-ℤ {x} {y} =
    div-sim-unit-ℤ (sim-unit-abs-ℤ x) (refl-sim-unit-ℤ y)
```

### If we have that `sim-unit-ℤ x y`, then they must differ only by sign

```agda
abstract
  is-plus-or-minus-sim-unit-ℤ :
    {x y : ℤ} → sim-unit-ℤ x y → is-plus-or-minus-ℤ x y
  is-plus-or-minus-sim-unit-ℤ {x} {y} H with ( is-decidable-is-zero-ℤ x)
  is-plus-or-minus-sim-unit-ℤ {x} {y} H | inl z =
    inl (z ∙ inv (is-zero-sim-unit-ℤ H z))
  is-plus-or-minus-sim-unit-ℤ {x} {y} H | inr nz
    with
    ( is-one-or-neg-one-is-unit-ℤ
      ( int-unit-ℤ (pr1 (H (λ u → nz (pr1 u)))))
      ( is-unit-int-unit-ℤ (pr1 (H (λ u → nz (pr1 u))))))
  is-plus-or-minus-sim-unit-ℤ {x} {y} H | inr nz | inl pos =
    inl
      ( equational-reasoning
        x
        ＝ one-ℤ *ℤ x
          by (inv (left-unit-law-mul-ℤ x))
        ＝ (int-unit-ℤ (pr1 (H (λ u → nz (pr1 u))))) *ℤ x
          by inv (ap (_*ℤ x) pos)
        ＝ y
          by pr2 (H (λ u → nz (pr1 u))))
  is-plus-or-minus-sim-unit-ℤ {x} {y} H | inr nz | inr p =
    inr
      ( equational-reasoning
        neg-ℤ x
        ＝ (int-unit-ℤ (pr1 (H (λ u → nz (pr1 u))))) *ℤ x
          by ap (_*ℤ x) (inv p)
        ＝ y
          by pr2 (H (λ u → nz (pr1 u))))
```

### If `sim-unit-ℤ x y` holds and both `x` and `y` have the same sign, then `x ＝ y`

```agda
abstract
  eq-sim-unit-is-nonnegative-ℤ :
    {a b : ℤ} → is-nonnegative-ℤ a → is-nonnegative-ℤ b → sim-unit-ℤ a b →
    a ＝ b
  eq-sim-unit-is-nonnegative-ℤ {a} {b} H H' K =
    rec-coproduct
      ( id)
      ( λ K' →
        eq-is-zero-ℤ
          ( is-zero-is-nonnegative-neg-is-nonnegative-ℤ H
            ( is-nonnegative-eq-ℤ (inv K') H'))
          ( is-zero-is-nonnegative-neg-is-nonnegative-ℤ H'
            ( is-nonnegative-eq-ℤ (inv (neg-neg-ℤ a) ∙ ap neg-ℤ K') H)))
      ( is-plus-or-minus-sim-unit-ℤ K)
```
