# Addition on the natural numbers

```agda
module elementary-number-theory.addition-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.functions
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.negation
open import foundation.universe-levels

open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Definition

```agda
add-ℕ : ℕ → ℕ → ℕ
add-ℕ x 0 = x
add-ℕ x (succ-ℕ y) = succ-ℕ (add-ℕ x y)

add-ℕ' : ℕ → ℕ → ℕ
add-ℕ' m n = add-ℕ n m

ap-add-ℕ :
  {m n m' n' : ℕ} → m ＝ m' → n ＝ n' → add-ℕ m n ＝ add-ℕ m' n'
ap-add-ℕ p q = ap-binary add-ℕ p q
```

## Properties

### The laws of addition on ℕ

```agda
right-unit-law-add-ℕ :
  (x : ℕ) → add-ℕ x zero-ℕ ＝ x
right-unit-law-add-ℕ x = refl

left-unit-law-add-ℕ :
  (x : ℕ) → add-ℕ zero-ℕ x ＝ x
left-unit-law-add-ℕ zero-ℕ = refl
left-unit-law-add-ℕ (succ-ℕ x) = ap succ-ℕ (left-unit-law-add-ℕ x)

left-successor-law-add-ℕ :
  (x y : ℕ) → add-ℕ (succ-ℕ x) y ＝ succ-ℕ (add-ℕ x y)
left-successor-law-add-ℕ x zero-ℕ = refl
left-successor-law-add-ℕ x (succ-ℕ y) =
  ap succ-ℕ (left-successor-law-add-ℕ x y)

right-successor-law-add-ℕ :
  (x y : ℕ) → add-ℕ x (succ-ℕ y) ＝ succ-ℕ (add-ℕ x y)
right-successor-law-add-ℕ x y = refl

associative-add-ℕ :
  (x y z : ℕ) → add-ℕ (add-ℕ x y) z ＝ add-ℕ x (add-ℕ y z)
associative-add-ℕ x y zero-ℕ = refl
associative-add-ℕ x y (succ-ℕ z) = ap succ-ℕ (associative-add-ℕ x y z)

commutative-add-ℕ : (x y : ℕ) → add-ℕ x y ＝ add-ℕ y x
commutative-add-ℕ zero-ℕ y = left-unit-law-add-ℕ y
commutative-add-ℕ (succ-ℕ x) y =
  (left-successor-law-add-ℕ x y) ∙ (ap succ-ℕ (commutative-add-ℕ x y))

left-one-law-add-ℕ :
  (x : ℕ) → add-ℕ 1 x ＝ succ-ℕ x
left-one-law-add-ℕ x =
  ( left-successor-law-add-ℕ zero-ℕ x) ∙
  ( ap succ-ℕ (left-unit-law-add-ℕ x))

right-one-law-add-ℕ :
  (x : ℕ) → add-ℕ x 1 ＝ succ-ℕ x
right-one-law-add-ℕ x = refl

left-two-law-add-ℕ :
  (x : ℕ) → add-ℕ 2 x ＝ succ-ℕ (succ-ℕ x)
left-two-law-add-ℕ x =
  ( left-successor-law-add-ℕ 1 x) ∙
  ( ap succ-ℕ (left-one-law-add-ℕ x))

right-two-law-add-ℕ :
  (x : ℕ) → add-ℕ x 2 ＝ succ-ℕ (succ-ℕ x)
right-two-law-add-ℕ x = refl

interchange-law-add-add-ℕ : interchange-law add-ℕ add-ℕ
interchange-law-add-add-ℕ =
  interchange-law-commutative-and-associative
    add-ℕ
    commutative-add-ℕ
    associative-add-ℕ

is-injective-add-ℕ' : (k : ℕ) → is-injective (add-ℕ' k)
is-injective-add-ℕ' zero-ℕ = id
is-injective-add-ℕ' (succ-ℕ k) p = is-injective-add-ℕ' k (is-injective-succ-ℕ p)

is-injective-add-ℕ : (k : ℕ) → is-injective (add-ℕ k)
is-injective-add-ℕ k {x} {y} p =
  is-injective-add-ℕ' k (commutative-add-ℕ x k ∙ (p ∙ commutative-add-ℕ k y))

is-emb-add-ℕ : (x : ℕ) → is-emb (add-ℕ x)
is-emb-add-ℕ x = is-emb-is-injective is-set-ℕ (is-injective-add-ℕ x)

is-emb-add-ℕ' : (x : ℕ) → is-emb (add-ℕ' x)
is-emb-add-ℕ' x = is-emb-is-injective is-set-ℕ (is-injective-add-ℕ' x)

is-zero-right-is-zero-add-ℕ :
  (x y : ℕ) → is-zero-ℕ (add-ℕ x y) → is-zero-ℕ y
is-zero-right-is-zero-add-ℕ x zero-ℕ p = refl
is-zero-right-is-zero-add-ℕ x (succ-ℕ y) p =
  ex-falso (is-nonzero-succ-ℕ (add-ℕ x y) p)

is-zero-left-is-zero-add-ℕ :
  (x y : ℕ) → is-zero-ℕ (add-ℕ x y) → is-zero-ℕ x
is-zero-left-is-zero-add-ℕ x y p =
  is-zero-right-is-zero-add-ℕ y x ((commutative-add-ℕ y x) ∙ p)

is-zero-summand-is-zero-sum-ℕ :
  (x y : ℕ) → is-zero-ℕ (add-ℕ x y) → (is-zero-ℕ x) × (is-zero-ℕ y)
is-zero-summand-is-zero-sum-ℕ x y p =
  pair (is-zero-left-is-zero-add-ℕ x y p) (is-zero-right-is-zero-add-ℕ x y p)

is-zero-sum-is-zero-summand-ℕ :
  (x y : ℕ) → (is-zero-ℕ x) × (is-zero-ℕ y) → is-zero-ℕ (add-ℕ x y)
is-zero-sum-is-zero-summand-ℕ .zero-ℕ .zero-ℕ (pair refl refl) = refl

neq-add-ℕ :
  (m n : ℕ) → ¬ (m ＝ add-ℕ m (succ-ℕ n))
neq-add-ℕ (succ-ℕ m) n p =
  neq-add-ℕ m n
    ( ( is-injective-succ-ℕ p) ∙
      ( left-successor-law-add-ℕ m n))
```

### The natural numbers with addition is a monoid

```agda
ℕ-Semigroup : Semigroup lzero
pr1 ℕ-Semigroup = ℕ-Set
pr1 (pr2 ℕ-Semigroup) = add-ℕ
pr2 (pr2 ℕ-Semigroup) = associative-add-ℕ

ℕ-Monoid : Monoid lzero
pr1 ℕ-Monoid = ℕ-Semigroup
pr1 (pr2 ℕ-Monoid) = 0
pr1 (pr2 (pr2 ℕ-Monoid)) = left-unit-law-add-ℕ
pr2 (pr2 (pr2 ℕ-Monoid)) = right-unit-law-add-ℕ
```
