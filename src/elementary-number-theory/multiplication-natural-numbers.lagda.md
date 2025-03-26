# Multiplication of natural numbers

```agda
module elementary-number-theory.multiplication-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.negated-equality
open import foundation.sets
```

</details>

## Idea

The {{#concept "multiplication" Disambiguation="natural numbers" Agda=mul-ℕ}}
operation on the [natural numbers](elementary-number-theory.natural-numbers.md)
is defined by [iteratively](foundation.iterating-functions.md) applying
[addition](elementary-number-theory.addition-natural-numbers.md) of a number to
itself. More preciesly the number `m * n` is defined by adding the number `n` to
itself `m` times:

```text
  m * n = n + ⋯ + n    (n added to itself m times).
```

## Definition

### Multiplication

```agda
mul-ℕ : ℕ → ℕ → ℕ
mul-ℕ 0 n = 0
mul-ℕ (succ-ℕ m) n = (mul-ℕ m n) +ℕ n

infixl 40 _*ℕ_
_*ℕ_ = mul-ℕ

{-# BUILTIN NATTIMES _*ℕ_ #-}

mul-ℕ' : ℕ → ℕ → ℕ
mul-ℕ' x y = mul-ℕ y x

ap-mul-ℕ :
  {x y x' y' : ℕ} → x ＝ x' → y ＝ y' → x *ℕ y ＝ x' *ℕ y'
ap-mul-ℕ p q = ap-binary mul-ℕ p q

double-ℕ : ℕ → ℕ
double-ℕ x = 2 *ℕ x

triple-ℕ : ℕ → ℕ
triple-ℕ x = 3 *ℕ x
```

## Properties

```agda
abstract
  left-zero-law-mul-ℕ :
    (x : ℕ) → zero-ℕ *ℕ x ＝ zero-ℕ
  left-zero-law-mul-ℕ x = refl

  right-zero-law-mul-ℕ :
    (x : ℕ) → x *ℕ zero-ℕ ＝ zero-ℕ
  right-zero-law-mul-ℕ zero-ℕ = refl
  right-zero-law-mul-ℕ (succ-ℕ x) =
    ( right-unit-law-add-ℕ (x *ℕ zero-ℕ)) ∙ (right-zero-law-mul-ℕ x)

abstract
  right-unit-law-mul-ℕ :
    (x : ℕ) → x *ℕ 1 ＝ x
  right-unit-law-mul-ℕ zero-ℕ = refl
  right-unit-law-mul-ℕ (succ-ℕ x) = ap succ-ℕ (right-unit-law-mul-ℕ x)

  left-unit-law-mul-ℕ :
    (x : ℕ) → 1 *ℕ x ＝ x
  left-unit-law-mul-ℕ zero-ℕ = refl
  left-unit-law-mul-ℕ (succ-ℕ x) = ap succ-ℕ (left-unit-law-mul-ℕ x)

abstract
  left-successor-law-mul-ℕ :
    (x y : ℕ) → (succ-ℕ x) *ℕ y ＝ (x *ℕ y) +ℕ y
  left-successor-law-mul-ℕ x y = refl

  right-successor-law-mul-ℕ :
    (x y : ℕ) → x *ℕ (succ-ℕ y) ＝ x +ℕ (x *ℕ y)
  right-successor-law-mul-ℕ zero-ℕ y = refl
  right-successor-law-mul-ℕ (succ-ℕ x) y =
    ( ( ap (λ t → succ-ℕ (t +ℕ y)) (right-successor-law-mul-ℕ x y)) ∙
      ( ap succ-ℕ (associative-add-ℕ x (x *ℕ y) y))) ∙
    ( inv (left-successor-law-add-ℕ x ((x *ℕ y) +ℕ y)))

abstract
  commutative-mul-ℕ :
    (x y : ℕ) → x *ℕ y ＝ y *ℕ x
  commutative-mul-ℕ zero-ℕ y = inv (right-zero-law-mul-ℕ y)
  commutative-mul-ℕ (succ-ℕ x) y =
    ( commutative-add-ℕ (x *ℕ y) y) ∙
    ( ( ap (y +ℕ_) (commutative-mul-ℕ x y)) ∙
      ( inv (right-successor-law-mul-ℕ y x)))

abstract
  left-distributive-mul-add-ℕ :
    (x y z : ℕ) → x *ℕ (y +ℕ z) ＝ (x *ℕ y) +ℕ (x *ℕ z)
  left-distributive-mul-add-ℕ zero-ℕ y z = refl
  left-distributive-mul-add-ℕ (succ-ℕ x) y z =
    ( left-successor-law-mul-ℕ x (y +ℕ z)) ∙
    ( ( ap (_+ℕ (y +ℕ z)) (left-distributive-mul-add-ℕ x y z)) ∙
      ( ( associative-add-ℕ (x *ℕ y) (x *ℕ z) (y +ℕ z)) ∙
        ( ( ap
            ( ( x *ℕ y) +ℕ_)
            ( ( inv (associative-add-ℕ (x *ℕ z) y z)) ∙
              ( ( ap (_+ℕ z) (commutative-add-ℕ (x *ℕ z) y)) ∙
                ( associative-add-ℕ y (x *ℕ z) z)))) ∙
          ( inv (associative-add-ℕ (x *ℕ y) y ((x *ℕ z) +ℕ z))))))

abstract
  right-distributive-mul-add-ℕ :
    (x y z : ℕ) → (x +ℕ y) *ℕ z ＝ (x *ℕ z) +ℕ (y *ℕ z)
  right-distributive-mul-add-ℕ x y z =
    ( commutative-mul-ℕ (x +ℕ y) z) ∙
    ( ( left-distributive-mul-add-ℕ z x y) ∙
      ( ( ap (_+ℕ (z *ℕ y)) (commutative-mul-ℕ z x)) ∙
        ( ap ((x *ℕ z) +ℕ_) (commutative-mul-ℕ z y))))

abstract
  associative-mul-ℕ :
    (x y z : ℕ) → (x *ℕ y) *ℕ z ＝ x *ℕ (y *ℕ z)
  associative-mul-ℕ zero-ℕ y z = refl
  associative-mul-ℕ (succ-ℕ x) y z =
    ( right-distributive-mul-add-ℕ (x *ℕ y) y z) ∙
    ( ap (_+ℕ (y *ℕ z)) (associative-mul-ℕ x y z))

left-two-law-mul-ℕ :
  (x : ℕ) → 2 *ℕ x ＝ x +ℕ x
left-two-law-mul-ℕ x =
  ( left-successor-law-mul-ℕ 1 x) ∙
  ( ap (_+ℕ x) (left-unit-law-mul-ℕ x))

right-two-law-mul-ℕ :
  (x : ℕ) → x *ℕ 2 ＝ x +ℕ x
right-two-law-mul-ℕ x =
  ( right-successor-law-mul-ℕ x 1) ∙
  ( ap (x +ℕ_) (right-unit-law-mul-ℕ x))

interchange-law-mul-mul-ℕ : interchange-law mul-ℕ mul-ℕ
interchange-law-mul-mul-ℕ =
  interchange-law-commutative-and-associative
    mul-ℕ
    commutative-mul-ℕ
    associative-mul-ℕ

is-injective-right-mul-succ-ℕ :
  (k : ℕ) → is-injective (_*ℕ (succ-ℕ k))
is-injective-right-mul-succ-ℕ k {zero-ℕ} {zero-ℕ} p = refl
is-injective-right-mul-succ-ℕ k {succ-ℕ m} {succ-ℕ n} p =
  ap succ-ℕ
    ( is-injective-right-mul-succ-ℕ k {m} {n}
      ( is-injective-right-add-ℕ
        ( succ-ℕ k)
        ( ( inv (left-successor-law-mul-ℕ m (succ-ℕ k))) ∙
          ( ( p) ∙
            ( left-successor-law-mul-ℕ n (succ-ℕ k))))))

is-injective-right-mul-ℕ : (k : ℕ) → is-nonzero-ℕ k → is-injective (_*ℕ k)
is-injective-right-mul-ℕ k H p with
  is-successor-is-nonzero-ℕ H
... | pair l refl = is-injective-right-mul-succ-ℕ l p

is-injective-left-mul-succ-ℕ :
  (k : ℕ) → is-injective ((succ-ℕ k) *ℕ_)
is-injective-left-mul-succ-ℕ k {m} {n} p =
  is-injective-right-mul-succ-ℕ k
    ( ( commutative-mul-ℕ m (succ-ℕ k)) ∙
      ( p ∙ commutative-mul-ℕ (succ-ℕ k) n))

is-injective-left-mul-ℕ :
  (k : ℕ) → is-nonzero-ℕ k → is-injective (k *ℕ_)
is-injective-left-mul-ℕ k H p with
  is-successor-is-nonzero-ℕ H
... | pair l refl = is-injective-left-mul-succ-ℕ l p

is-emb-left-mul-ℕ : (x : ℕ) → is-nonzero-ℕ x → is-emb (x *ℕ_)
is-emb-left-mul-ℕ x H =
  is-emb-is-injective is-set-ℕ (is-injective-left-mul-ℕ x H)

is-emb-right-mul-ℕ : (x : ℕ) → is-nonzero-ℕ x → is-emb (_*ℕ x)
is-emb-right-mul-ℕ x H =
  is-emb-is-injective is-set-ℕ (is-injective-right-mul-ℕ x H)

is-nonzero-mul-ℕ :
  (x y : ℕ) → is-nonzero-ℕ x → is-nonzero-ℕ y → is-nonzero-ℕ (x *ℕ y)
is-nonzero-mul-ℕ x y H K p =
  K (is-injective-left-mul-ℕ x H (p ∙ (inv (right-zero-law-mul-ℕ x))))

is-nonzero-left-factor-mul-ℕ :
  (x y : ℕ) → is-nonzero-ℕ (x *ℕ y) → is-nonzero-ℕ x
is-nonzero-left-factor-mul-ℕ .zero-ℕ y H refl = H (left-zero-law-mul-ℕ y)

is-nonzero-right-factor-mul-ℕ :
  (x y : ℕ) → is-nonzero-ℕ (x *ℕ y) → is-nonzero-ℕ y
is-nonzero-right-factor-mul-ℕ x .zero-ℕ H refl = H (right-zero-law-mul-ℕ x)
```

We conclude that $y = 1$ if $(x+1)y = x+1$.

```agda
is-one-is-right-unit-mul-ℕ :
  (x y : ℕ) → (succ-ℕ x) *ℕ y ＝ succ-ℕ x → is-one-ℕ y
is-one-is-right-unit-mul-ℕ x y p =
  is-injective-left-mul-succ-ℕ x (p ∙ inv (right-unit-law-mul-ℕ (succ-ℕ x)))

is-one-is-left-unit-mul-ℕ :
  (x y : ℕ) → x *ℕ (succ-ℕ y) ＝ succ-ℕ y → is-one-ℕ x
is-one-is-left-unit-mul-ℕ x y p =
  is-injective-right-mul-succ-ℕ y (p ∙ inv (left-unit-law-mul-ℕ (succ-ℕ y)))

is-one-right-is-one-mul-ℕ :
  (x y : ℕ) → is-one-ℕ (x *ℕ y) → is-one-ℕ y
is-one-right-is-one-mul-ℕ zero-ℕ zero-ℕ p = p
is-one-right-is-one-mul-ℕ zero-ℕ (succ-ℕ y) ()
is-one-right-is-one-mul-ℕ (succ-ℕ x) zero-ℕ p =
  is-one-right-is-one-mul-ℕ x zero-ℕ p
is-one-right-is-one-mul-ℕ (succ-ℕ x) (succ-ℕ y) p =
  ap
    ( succ-ℕ)
    ( is-zero-right-is-zero-add-ℕ (x *ℕ (succ-ℕ y)) y
      ( is-injective-succ-ℕ p))

is-one-left-is-one-mul-ℕ :
  (x y : ℕ) → is-one-ℕ (x *ℕ y) → is-one-ℕ x
is-one-left-is-one-mul-ℕ x y p =
  is-one-right-is-one-mul-ℕ y x (commutative-mul-ℕ y x ∙ p)

is-one-mul-ℕ :
  (x y : ℕ) → is-one-ℕ x → is-one-ℕ y → is-one-ℕ (x *ℕ y)
is-one-mul-ℕ .1 .1 refl refl = refl

neq-mul-ℕ :
  (m n : ℕ) → succ-ℕ m ≠ (succ-ℕ m *ℕ (succ-ℕ (succ-ℕ n)))
neq-mul-ℕ m n p =
  neq-add-ℕ
    ( succ-ℕ m)
    ( ( m *ℕ (succ-ℕ n)) +ℕ n)
    ( ( p) ∙
      ( ( right-successor-law-mul-ℕ (succ-ℕ m) (succ-ℕ n)) ∙
        ( ap ((succ-ℕ m) +ℕ_) (left-successor-law-mul-ℕ m (succ-ℕ n)))))
```

### Either of the factors is zero if and only if the product is zero

```agda
is-zero-summand-is-zero-mul-ℕ :
  (x y : ℕ) → is-zero-ℕ (x *ℕ y) → is-zero-ℕ x + is-zero-ℕ y
is-zero-summand-is-zero-mul-ℕ 0 y H = inl refl
is-zero-summand-is-zero-mul-ℕ (succ-ℕ x) 0 H = inr refl

is-zero-mul-ℕ-is-zero-left-summand :
  (x y : ℕ) → is-zero-ℕ x → is-zero-ℕ (x *ℕ y)
is-zero-mul-ℕ-is-zero-left-summand .0 y refl = left-zero-law-mul-ℕ y

is-zero-mul-ℕ-is-zero-right-summand :
  (x y : ℕ) → is-zero-ℕ y → is-zero-ℕ (x *ℕ y)
is-zero-mul-ℕ-is-zero-right-summand x .0 refl = right-zero-law-mul-ℕ x

is-zero-mul-ℕ-is-zero-summand :
  (x y : ℕ) → is-zero-ℕ x + is-zero-ℕ y → is-zero-ℕ (x *ℕ y)
is-zero-mul-ℕ-is-zero-summand x y (inl H) =
  is-zero-mul-ℕ-is-zero-left-summand x y H
is-zero-mul-ℕ-is-zero-summand x y (inr H) =
  is-zero-mul-ℕ-is-zero-right-summand x y H
```

## See also

- [Squares of natural numbers](elementary-number-theory.squares-natural-numbers.md)
- [Cubes of natural numbers](elementary-number-theory.cubes-natural-numbers.md)
