# Addition on the integers

```agda
module elementary-number-theory.addition-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equational-reasoning
open import foundation.equivalences
open import foundation.functions
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.pointed-types-equipped-with-automorphisms
```

</details>

## Idea

We introduce addition on the integers and derive its basic properties with respect to `succ-ℤ` and `neg-ℤ`. Properties of addition with respect to inequality are derived in `inequality-integers`.

## Definition

```agda
add-ℤ : ℤ → ℤ → ℤ
add-ℤ (inl zero-ℕ) l = pred-ℤ l
add-ℤ (inl (succ-ℕ x)) l = pred-ℤ (add-ℤ (inl x) l)
add-ℤ (inr (inl star)) l = l
add-ℤ (inr (inr zero-ℕ)) l = succ-ℤ l
add-ℤ (inr (inr (succ-ℕ x))) l = succ-ℤ (add-ℤ (inr (inr x)) l)

add-ℤ' : ℤ → ℤ → ℤ
add-ℤ' x y = add-ℤ y x

infix 30 _+ℤ_
_+ℤ_ = add-ℤ

ap-add-ℤ :
  {x y x' y' : ℤ} → x ＝ x' → y ＝ y' → add-ℤ x y ＝ add-ℤ x' y'
ap-add-ℤ p q = ap-binary add-ℤ p q
```

## Properties

### Unit laws

```agda
abstract
  left-unit-law-add-ℤ : (k : ℤ) → zero-ℤ +ℤ k ＝ k
  left-unit-law-add-ℤ k = refl

  right-unit-law-add-ℤ : (k : ℤ) → k +ℤ zero-ℤ ＝ k
  right-unit-law-add-ℤ (inl zero-ℕ) = refl
  right-unit-law-add-ℤ (inl (succ-ℕ x)) =
    ap pred-ℤ (right-unit-law-add-ℤ (inl x))
  right-unit-law-add-ℤ (inr (inl star)) = refl
  right-unit-law-add-ℤ (inr (inr zero-ℕ)) = refl
  right-unit-law-add-ℤ (inr (inr (succ-ℕ x))) =
    ap succ-ℤ (right-unit-law-add-ℤ (inr (inr x)))
```

### Left and right predecessor laws

```agda
abstract
  left-predecessor-law-add-ℤ :
    (x y : ℤ) → pred-ℤ x +ℤ y ＝ pred-ℤ (x +ℤ y)
  left-predecessor-law-add-ℤ (inl n) y = refl
  left-predecessor-law-add-ℤ (inr (inl star)) y = refl
  left-predecessor-law-add-ℤ (inr (inr zero-ℕ)) y =
    inv (isretr-pred-ℤ y)
  left-predecessor-law-add-ℤ (inr (inr (succ-ℕ x))) y =
    inv (isretr-pred-ℤ (add-ℤ (inr (inr x)) y))

  right-predecessor-law-add-ℤ :
    (x y : ℤ) → x +ℤ pred-ℤ y ＝ pred-ℤ (x +ℤ y)
  right-predecessor-law-add-ℤ (inl zero-ℕ) n = refl
  right-predecessor-law-add-ℤ (inl (succ-ℕ m)) n =
    ap pred-ℤ (right-predecessor-law-add-ℤ (inl m) n)
  right-predecessor-law-add-ℤ (inr (inl star)) n = refl
  right-predecessor-law-add-ℤ (inr (inr zero-ℕ)) n =
    equational-reasoning
      succ-ℤ (pred-ℤ n)
      ＝ n                                       by issec-pred-ℤ n
      ＝ pred-ℤ (succ-ℤ n)                       by inv (isretr-pred-ℤ n)
  right-predecessor-law-add-ℤ (inr (inr (succ-ℕ x))) n =
    equational-reasoning
      succ-ℤ (inr (inr x) +ℤ pred-ℤ n)
      ＝ succ-ℤ (pred-ℤ (inr (inr x) +ℤ n))      by ap succ-ℤ (right-predecessor-law-add-ℤ (inr (inr x)) n)
      ＝ inr (inr x) +ℤ n                        by issec-pred-ℤ (add-ℤ (inr (inr x)) n)
      ＝ pred-ℤ (succ-ℤ (inr (inr x) +ℤ n))      by inv (isretr-pred-ℤ (add-ℤ (inr (inr x)) n))
```

### Left and right successor laws

```agda
abstract
  left-successor-law-add-ℤ :
    (x y : ℤ) → succ-ℤ x +ℤ y ＝ succ-ℤ (x +ℤ y)
  left-successor-law-add-ℤ (inl zero-ℕ) y =
    inv (issec-pred-ℤ y)
  left-successor-law-add-ℤ (inl (succ-ℕ x)) y =
    equational-reasoning
      inl x +ℤ y
      ＝ succ-ℤ (pred-ℤ (inl x +ℤ y))            by inv (issec-pred-ℤ (add-ℤ (inl x) y))
      ＝ succ-ℤ (pred-ℤ (inl x) +ℤ y)            by ap succ-ℤ (inv (left-predecessor-law-add-ℤ (inl x) y))
  left-successor-law-add-ℤ (inr (inl star)) y = refl
  left-successor-law-add-ℤ (inr (inr x)) y = refl

  right-successor-law-add-ℤ :
    (x y : ℤ) → x +ℤ succ-ℤ y ＝ succ-ℤ (x +ℤ y)
  right-successor-law-add-ℤ (inl zero-ℕ) y =
    equational-reasoning
      pred-ℤ (succ-ℤ y) ＝ y                     by isretr-pred-ℤ y
                        ＝ succ-ℤ (pred-ℤ y)     by inv (issec-pred-ℤ y)
  right-successor-law-add-ℤ (inl (succ-ℕ x)) y =
    equational-reasoning
      pred-ℤ (inl x +ℤ succ-ℤ y)
      ＝ pred-ℤ (succ-ℤ (inl x +ℤ y))            by ap pred-ℤ (right-successor-law-add-ℤ (inl x) y)
      ＝ inl x +ℤ y                              by isretr-pred-ℤ (add-ℤ (inl x) y)
      ＝ succ-ℤ (pred-ℤ (inl x +ℤ y))            by inv (issec-pred-ℤ (add-ℤ (inl x) y))
  right-successor-law-add-ℤ (inr (inl star)) y = refl
  right-successor-law-add-ℤ (inr (inr zero-ℕ)) y = refl
  right-successor-law-add-ℤ (inr (inr (succ-ℕ x))) y =
    ap succ-ℤ (right-successor-law-add-ℤ (inr (inr x)) y)
```

### The successor of an integer is that integer plus one

```agda
abstract
  is-add-one-succ-ℤ' : (x : ℤ) → succ-ℤ x ＝ x +ℤ one-ℤ
  is-add-one-succ-ℤ' x =
    equational-reasoning
      succ-ℤ x ＝ succ-ℤ (x +ℤ zero-ℤ)           by inv (ap succ-ℤ (right-unit-law-add-ℤ x))
               ＝ x +ℤ one-ℤ                     by inv (right-successor-law-add-ℤ x zero-ℤ)

  is-add-one-succ-ℤ : (x : ℤ) → succ-ℤ x ＝ one-ℤ +ℤ x
  is-add-one-succ-ℤ x = inv (left-successor-law-add-ℤ zero-ℤ x)

  add-one-left-ℤ : (x : ℤ) → one-ℤ +ℤ x ＝ succ-ℤ x
  add-one-left-ℤ x = refl

  add-one-right-ℤ : (x : ℤ) → x +ℤ one-ℤ ＝ succ-ℤ x
  add-one-right-ℤ x = inv (is-add-one-succ-ℤ' x)
```

### The predecessor of an integer is that integer minus one

```agda
  is-add-neg-one-pred-ℤ : (x : ℤ) → pred-ℤ x ＝ neg-one-ℤ +ℤ x
  is-add-neg-one-pred-ℤ x =
    inv (left-predecessor-law-add-ℤ zero-ℤ x)

  is-add-neg-one-pred-ℤ' : (x : ℤ) → pred-ℤ x ＝ x +ℤ neg-one-ℤ
  is-add-neg-one-pred-ℤ' x =
    equational-reasoning
      pred-ℤ x ＝ pred-ℤ (x +ℤ zero-ℤ)           by inv (ap pred-ℤ (right-unit-law-add-ℤ x))
               ＝ x +ℤ neg-one-ℤ                 by inv (right-predecessor-law-add-ℤ x zero-ℤ)

  add-neg-one-left-ℤ : (x : ℤ) → neg-one-ℤ +ℤ x ＝ pred-ℤ x
  add-neg-one-left-ℤ x = refl

  add-neg-one-right-ℤ : (x : ℤ) → x +ℤ neg-one-ℤ ＝ pred-ℤ x
  add-neg-one-right-ℤ x = inv (is-add-neg-one-pred-ℤ' x)
```

### Addition is associative

```agda
abstract
  associative-add-ℤ :
    (x y z : ℤ) → ((x +ℤ y) +ℤ z) ＝ (x +ℤ (y +ℤ z))
  associative-add-ℤ (inl zero-ℕ) y z =
    equational-reasoning
      (neg-one-ℤ +ℤ y) +ℤ z
      ＝ (pred-ℤ (zero-ℤ +ℤ y)) +ℤ z             by ap (add-ℤ' z) (left-predecessor-law-add-ℤ zero-ℤ y)
      ＝ pred-ℤ (y +ℤ z)                         by left-predecessor-law-add-ℤ y z
      ＝ neg-one-ℤ +ℤ (y +ℤ z)                   by inv (left-predecessor-law-add-ℤ zero-ℤ (add-ℤ y z))
  associative-add-ℤ (inl (succ-ℕ x)) y z =
    equational-reasoning
      (pred-ℤ (inl x) +ℤ y) +ℤ z
      ＝ pred-ℤ (inl x +ℤ y) +ℤ z                by ap (add-ℤ' z) (left-predecessor-law-add-ℤ (inl x) y)
      ＝ pred-ℤ ((inl x +ℤ y) +ℤ z)              by left-predecessor-law-add-ℤ (add-ℤ (inl x) y) z
      ＝ pred-ℤ (inl x +ℤ (y +ℤ z))              by ap pred-ℤ (associative-add-ℤ (inl x) y z)
      ＝ pred-ℤ (inl x) +ℤ (y +ℤ z)              by inv (left-predecessor-law-add-ℤ (inl x) (add-ℤ y z))
  associative-add-ℤ (inr (inl star)) y z =
    refl
  associative-add-ℤ (inr (inr zero-ℕ)) y z =
    equational-reasoning
      (one-ℤ +ℤ y) +ℤ z
      ＝ succ-ℤ (zero-ℤ +ℤ y) +ℤ z               by ap (add-ℤ' z) (left-successor-law-add-ℤ zero-ℤ y)
      ＝ succ-ℤ (y +ℤ z)                         by left-successor-law-add-ℤ y z
      ＝ one-ℤ +ℤ (y +ℤ z)                       by inv (left-successor-law-add-ℤ zero-ℤ (add-ℤ y z))
  associative-add-ℤ (inr (inr (succ-ℕ x))) y z =
    equational-reasoning
      (succ-ℤ (inr (inr x)) +ℤ y) +ℤ z
      ＝ succ-ℤ (inr (inr x) +ℤ y) +ℤ z          by ap (add-ℤ' z) (left-successor-law-add-ℤ (inr (inr x)) y)
      ＝ succ-ℤ ((inr (inr x) +ℤ y) +ℤ z)        by left-successor-law-add-ℤ (add-ℤ (inr (inr x)) y) z
      ＝ succ-ℤ (inr (inr x) +ℤ (y +ℤ z))        by ap succ-ℤ (associative-add-ℤ (inr (inr x)) y z)
      ＝ succ-ℤ (inr (inr x)) +ℤ (y +ℤ z)        by inv (left-successor-law-add-ℤ (inr (inr x)) (add-ℤ y z))
```

### Addition is commutative

```agda
abstract
  commutative-add-ℤ : (x y : ℤ) → x +ℤ y ＝ y +ℤ x
  commutative-add-ℤ (inl zero-ℕ) y =
    equational-reasoning
      add-ℤ neg-one-ℤ y
      ＝ pred-ℤ (add-ℤ zero-ℤ y)                 by left-predecessor-law-add-ℤ zero-ℤ y
      ＝ pred-ℤ (add-ℤ y zero-ℤ)                 by inv (ap pred-ℤ (right-unit-law-add-ℤ y))
      ＝ add-ℤ y neg-one-ℤ                       by inv (right-predecessor-law-add-ℤ y zero-ℤ)
  commutative-add-ℤ (inl (succ-ℕ x)) y =
    equational-reasoning
      add-ℤ (inl (succ-ℕ x)) y
      ＝ pred-ℤ (add-ℤ y (inl x))                by ap pred-ℤ (commutative-add-ℤ (inl x) y)
      ＝ add-ℤ y (inl (succ-ℕ x))                by inv (right-predecessor-law-add-ℤ y (inl x))
  commutative-add-ℤ (inr (inl star)) y =
    inv (right-unit-law-add-ℤ y)
  commutative-add-ℤ (inr (inr zero-ℕ)) y =
    equational-reasoning
      succ-ℤ y
      ＝ succ-ℤ (add-ℤ y zero-ℤ)                 by inv (ap succ-ℤ (right-unit-law-add-ℤ y))
      ＝ add-ℤ y one-ℤ                           by inv (right-successor-law-add-ℤ y zero-ℤ)
  commutative-add-ℤ (inr (inr (succ-ℕ x))) y =
    equational-reasoning
      succ-ℤ (add-ℤ (inr (inr x)) y)
      ＝ succ-ℤ (add-ℤ y (inr (inr x)))          by ap succ-ℤ (commutative-add-ℤ (inr (inr x)) y)
      ＝ add-ℤ y (succ-ℤ (inr (inr x)))          by inv (right-successor-law-add-ℤ y (inr (inr x)))
```

### The inverse laws for addition and negatives

```agda
abstract
  left-inverse-law-add-ℤ :
    (x : ℤ) → neg-ℤ x +ℤ x ＝ zero-ℤ
  left-inverse-law-add-ℤ (inl zero-ℕ) = refl
  left-inverse-law-add-ℤ (inl (succ-ℕ x)) =
    equational-reasoning
      succ-ℤ (inr (inr x) +ℤ pred-ℤ (inl x))
      ＝ succ-ℤ (pred-ℤ (inr (inr x) +ℤ inl x))  by ap succ-ℤ (right-predecessor-law-add-ℤ (inr (inr x)) (inl x))
      ＝ inr (inr x) +ℤ inl x                    by issec-pred-ℤ (add-ℤ (inr (inr x)) (inl x))
      ＝ zero-ℤ                                  by left-inverse-law-add-ℤ (inl x)
  left-inverse-law-add-ℤ (inr (inl star)) = refl
  left-inverse-law-add-ℤ (inr (inr x)) =
    equational-reasoning
      neg-ℤ (inr (inr x)) +ℤ inr (inr x)
      ＝ inr (inr x) +ℤ inl x                    by commutative-add-ℤ (inl x) (inr (inr x))
      ＝ zero-ℤ                                  by left-inverse-law-add-ℤ (inl x)

  right-inverse-law-add-ℤ :
    (x : ℤ) → x +ℤ neg-ℤ x ＝ zero-ℤ
  right-inverse-law-add-ℤ x =
    equational-reasoning
      x +ℤ neg-ℤ x ＝ neg-ℤ x +ℤ x               by commutative-add-ℤ x (neg-ℤ x)
                   ＝ zero-ℤ                     by left-inverse-law-add-ℤ x
```

### Interchange law for addition with respect to addition

```agda
interchange-law-add-add-ℤ : interchange-law add-ℤ add-ℤ
interchange-law-add-add-ℤ =
  interchange-law-commutative-and-associative
    add-ℤ
    commutative-add-ℤ
    associative-add-ℤ
```

### Addition by x is a binary equivalence

```agda
issec-add-neg-ℤ :
  (x y : ℤ) → x +ℤ (neg-ℤ x +ℤ y) ＝ y
issec-add-neg-ℤ x y =
  equational-reasoning
    x +ℤ (neg-ℤ x +ℤ y) ＝ (x +ℤ neg-ℤ x) +ℤ y   by inv (associative-add-ℤ x (neg-ℤ x) y)
                        ＝ y                     by ap (add-ℤ' y) (right-inverse-law-add-ℤ x)

isretr-add-neg-ℤ :
  (x y : ℤ) → add-ℤ (neg-ℤ x) (add-ℤ x y) ＝ y
isretr-add-neg-ℤ x y =
  equational-reasoning
    neg-ℤ x +ℤ (x +ℤ y) ＝ (neg-ℤ x +ℤ x) +ℤ y   by inv (associative-add-ℤ (neg-ℤ x) x y)
                        ＝ y                     by ap (add-ℤ' y) (left-inverse-law-add-ℤ x)

abstract
  is-equiv-add-ℤ : (x : ℤ) → is-equiv (add-ℤ x)
  pr1 (pr1 (is-equiv-add-ℤ x)) = add-ℤ (neg-ℤ x)
  pr2 (pr1 (is-equiv-add-ℤ x)) = issec-add-neg-ℤ x
  pr1 (pr2 (is-equiv-add-ℤ x)) = add-ℤ (neg-ℤ x)
  pr2 (pr2 (is-equiv-add-ℤ x)) = isretr-add-neg-ℤ x

equiv-add-ℤ : ℤ → (ℤ ≃ ℤ)
pr1 (equiv-add-ℤ x) = add-ℤ x
pr2 (equiv-add-ℤ x) = is-equiv-add-ℤ x

issec-add-neg-ℤ' :
  (x y : ℤ) → (y +ℤ neg-ℤ x) +ℤ x ＝ y
issec-add-neg-ℤ' x y =
  equational-reasoning
    (y +ℤ neg-ℤ x) +ℤ x ＝ y +ℤ (neg-ℤ x +ℤ x)   by associative-add-ℤ y (neg-ℤ x) x
                        ＝ y +ℤ zero-ℤ           by ap (add-ℤ y) (left-inverse-law-add-ℤ x)
                        ＝ y                     by right-unit-law-add-ℤ y

isretr-add-neg-ℤ' :
  (x y : ℤ) → (y +ℤ x) +ℤ neg-ℤ x ＝ y
isretr-add-neg-ℤ' x y =
  equational-reasoning
    (y +ℤ x) +ℤ neg-ℤ x ＝ y +ℤ (x +ℤ neg-ℤ x)   by associative-add-ℤ y x (neg-ℤ x)
                        ＝ y +ℤ zero-ℤ           by ap (add-ℤ y) (right-inverse-law-add-ℤ x)
                        ＝ y                     by right-unit-law-add-ℤ y

abstract
  is-equiv-add-ℤ' : (y : ℤ) → is-equiv (add-ℤ' y)
  pr1 (pr1 (is-equiv-add-ℤ' y)) = add-ℤ' (neg-ℤ y)
  pr2 (pr1 (is-equiv-add-ℤ' y)) = issec-add-neg-ℤ' y
  pr1 (pr2 (is-equiv-add-ℤ' y)) = add-ℤ' (neg-ℤ y)
  pr2 (pr2 (is-equiv-add-ℤ' y)) = isretr-add-neg-ℤ' y

equiv-add-ℤ' : ℤ → (ℤ ≃ ℤ)
pr1 (equiv-add-ℤ' y) = add-ℤ' y
pr2 (equiv-add-ℤ' y) = is-equiv-add-ℤ' y

is-binary-equiv-add-ℤ : is-binary-equiv add-ℤ
pr1 is-binary-equiv-add-ℤ = is-equiv-add-ℤ'
pr2 is-binary-equiv-add-ℤ = is-equiv-add-ℤ
```

### Addition by an integer is a binary embedding

```agda
is-emb-add-ℤ :
  (x : ℤ) → is-emb (add-ℤ x)
is-emb-add-ℤ x =
  is-emb-is-equiv (is-equiv-add-ℤ x)

is-emb-add-ℤ' :
  (y : ℤ) → is-emb (add-ℤ' y)
is-emb-add-ℤ' y = is-emb-is-equiv (is-equiv-add-ℤ' y)

is-binary-emb-add-ℤ : is-binary-emb add-ℤ
is-binary-emb-add-ℤ =
  is-binary-emb-is-binary-equiv is-binary-equiv-add-ℤ
```

### Addition by x is injective

```agda
is-injective-add-ℤ' : (x : ℤ) → is-injective (add-ℤ' x)
is-injective-add-ℤ' x = is-injective-is-emb (is-emb-add-ℤ' x)

is-injective-add-ℤ : (x : ℤ) → is-injective (add-ℤ x)
is-injective-add-ℤ x = is-injective-is-emb (is-emb-add-ℤ x)
```

### Negative laws for addition

```agda
right-negative-law-add-ℤ :
  (k l : ℤ) → k +ℤ neg-ℤ l ＝ neg-ℤ (neg-ℤ k +ℤ l)
right-negative-law-add-ℤ (inl zero-ℕ) l =
  equational-reasoning
    neg-one-ℤ +ℤ neg-ℤ l
    ＝ pred-ℤ (zero-ℤ +ℤ neg-ℤ l)                by left-predecessor-law-add-ℤ zero-ℤ (neg-ℤ l)
    ＝ neg-ℤ (succ-ℤ l)                          by pred-neg-ℤ l
right-negative-law-add-ℤ (inl (succ-ℕ x)) l =
  equational-reasoning
    pred-ℤ (inl x) +ℤ neg-ℤ l
    ＝ pred-ℤ (inl x +ℤ neg-ℤ l)                 by left-predecessor-law-add-ℤ (inl x) (neg-ℤ l)
    ＝ pred-ℤ (neg-ℤ (neg-ℤ (inl x) +ℤ l))       by ap pred-ℤ (right-negative-law-add-ℤ (inl x) l)
    ＝ neg-ℤ (succ-ℤ (inr (inr x) +ℤ l))         by pred-neg-ℤ (inr (inr x) +ℤ l)
right-negative-law-add-ℤ (inr (inl star)) l =
  refl
right-negative-law-add-ℤ (inr (inr zero-ℕ)) l =
  inv (neg-pred-ℤ l)
right-negative-law-add-ℤ (inr (inr (succ-ℕ n))) l =
  equational-reasoning
    succ-ℤ (in-pos n) +ℤ neg-ℤ l
    ＝ succ-ℤ (in-pos n +ℤ neg-ℤ l)              by left-successor-law-add-ℤ (in-pos n) (neg-ℤ l)
    ＝ succ-ℤ (neg-ℤ (neg-ℤ (inr (inr n)) +ℤ l)) by ap succ-ℤ (right-negative-law-add-ℤ (inr (inr n)) l)
    ＝ neg-ℤ (pred-ℤ (add-ℤ (inl n) l))          by inv (neg-pred-ℤ (add-ℤ (inl n) l))
```

### Distributivity of negatives over addition

```agda
distributive-neg-add-ℤ :
  (k l : ℤ) → neg-ℤ (k +ℤ l) ＝ neg-ℤ k +ℤ neg-ℤ l
distributive-neg-add-ℤ (inl zero-ℕ) l =
  equational-reasoning
    neg-ℤ (inl zero-ℕ +ℤ l)
    ＝ neg-ℤ (pred-ℤ (zero-ℤ +ℤ l))              by ap neg-ℤ (left-predecessor-law-add-ℤ zero-ℤ l)
    ＝ neg-ℤ (inl zero-ℕ) +ℤ neg-ℤ l             by neg-pred-ℤ l
distributive-neg-add-ℤ (inl (succ-ℕ n)) l =
  equational-reasoning
    neg-ℤ (pred-ℤ (inl n +ℤ l))
    ＝ succ-ℤ (neg-ℤ (inl n +ℤ l))               by neg-pred-ℤ (inl n +ℤ l)
    ＝ succ-ℤ (neg-ℤ (inl n) +ℤ neg-ℤ l)         by ap succ-ℤ (distributive-neg-add-ℤ (inl n) l)
    ＝ neg-ℤ (pred-ℤ (inl n)) +ℤ neg-ℤ l         by ap (add-ℤ' (neg-ℤ l)) (inv (neg-pred-ℤ (inl n)))
distributive-neg-add-ℤ (inr (inl star)) l =
  refl
distributive-neg-add-ℤ (inr (inr zero-ℕ)) l =
  inv (pred-neg-ℤ l)
distributive-neg-add-ℤ (inr (inr (succ-ℕ n))) l =
  equational-reasoning
    neg-ℤ (succ-ℤ (in-pos n +ℤ l))
    ＝ pred-ℤ (neg-ℤ (in-pos n +ℤ l))            by inv (pred-neg-ℤ (in-pos n +ℤ l))
    ＝ pred-ℤ (neg-ℤ (inr (inr n)) +ℤ neg-ℤ l)   by ap pred-ℤ (distributive-neg-add-ℤ (inr (inr n)) l)
```

### Addition of nonnegative integers is nonnegative

```agda
is-nonnegative-add-ℤ :
  (k l : ℤ) →
  is-nonnegative-ℤ k → is-nonnegative-ℤ l → is-nonnegative-ℤ (add-ℤ k l)
is-nonnegative-add-ℤ (inr (inl star)) (inr (inl star)) p q = star
is-nonnegative-add-ℤ (inr (inl star)) (inr (inr n)) p q = star
is-nonnegative-add-ℤ (inr (inr zero-ℕ)) (inr (inl star)) p q = star
is-nonnegative-add-ℤ (inr (inr (succ-ℕ n))) (inr (inl star)) star star =
  is-nonnegative-succ-ℤ
    ( add-ℤ (inr (inr n)) (inr (inl star)))
    ( is-nonnegative-add-ℤ (inr (inr n)) (inr (inl star)) star star)
is-nonnegative-add-ℤ (inr (inr zero-ℕ)) (inr (inr m)) star star = star
is-nonnegative-add-ℤ (inr (inr (succ-ℕ n))) (inr (inr m)) star star =
  is-nonnegative-succ-ℤ
    ( add-ℤ (inr (inr n)) (inr (inr m)))
    ( is-nonnegative-add-ℤ (inr (inr n)) (inr (inr m)) star star)
```

### Addition of positive integers is positive

```agda
is-positive-add-ℤ :
  {x y : ℤ} → is-positive-ℤ x → is-positive-ℤ y → is-positive-ℤ (add-ℤ x y)
is-positive-add-ℤ {inr (inr zero-ℕ)} {inr (inr y)} H K = star
is-positive-add-ℤ {inr (inr (succ-ℕ x))} {inr (inr y)} H K =
  is-positive-succ-ℤ
    ( is-nonnegative-is-positive-ℤ
      ( is-positive-add-ℤ {inr (inr x)} {inr (inr y)} star star))
```

### The inclusion of ℕ into ℤ preserves addition

```agda
add-int-ℕ : (x y : ℕ) → add-ℤ (int-ℕ x) (int-ℕ y) ＝ int-ℕ (add-ℕ x y)
add-int-ℕ x zero-ℕ = right-unit-law-add-ℤ (int-ℕ x)
add-int-ℕ x (succ-ℕ y) =
  equational-reasoning
    int-ℕ x +ℤ int-ℕ (succ-ℕ y)
    ＝ int-ℕ x +ℤ succ-ℤ (int-ℕ y)               by ap (add-ℤ (int-ℕ x)) (inv (succ-int-ℕ y))
    ＝ succ-ℤ (int-ℕ x +ℤ int-ℕ y)               by right-successor-law-add-ℤ (int-ℕ x) (int-ℕ y)
    ＝ succ-ℤ (int-ℕ (add-ℕ x y))                by ap succ-ℤ (add-int-ℕ x y)
    ＝ int-ℕ (succ-ℕ (add-ℕ x y))                by succ-int-ℕ (add-ℕ x y)
```

### If `x+y=y` then `x=0`

```agda
is-zero-add-ℤ :
  (x y : ℤ) → add-ℤ x y ＝ y → is-zero-ℤ x
is-zero-add-ℤ x y H =
  equational-reasoning
    x ＝ x +ℤ zero-ℤ                             by inv (right-unit-law-add-ℤ x)
      ＝ x +ℤ (y +ℤ neg-ℤ y)                     by inv (ap (add-ℤ x) (right-inverse-law-add-ℤ y))
      ＝ (x +ℤ y) +ℤ neg-ℤ y                     by inv (associative-add-ℤ x y (neg-ℤ y))
      ＝ y +ℤ neg-ℤ y                            by ap (add-ℤ' (neg-ℤ y)) H
      ＝ zero-ℤ                                  by right-inverse-law-add-ℤ y

is-zero-add-ℤ' :
  (x y : ℤ) → add-ℤ x y ＝ x → is-zero-ℤ y
is-zero-add-ℤ' x y H =
  is-zero-add-ℤ y x (commutative-add-ℤ y x ∙ H)
```

### Adding negatives results in a negative

```agda
negatives-add-ℤ :
  (x y : ℕ) → in-neg x +ℤ in-neg y ＝ in-neg (succ-ℕ (add-ℕ x y))
negatives-add-ℤ zero-ℕ y = ap (inl ∘ succ-ℕ) (inv (left-unit-law-add-ℕ y))
negatives-add-ℤ (succ-ℕ x) y =
  equational-reasoning
    pred-ℤ (in-neg x +ℤ in-neg y)
    ＝ pred-ℤ (in-neg (succ-ℕ (add-ℕ x y)))      by ap pred-ℤ (negatives-add-ℤ x y)
    ＝ (inl ∘ succ-ℕ) (add-ℕ (succ-ℕ x) y)       by ap (inl ∘ succ-ℕ) (inv (left-successor-law-add-ℕ x y))
```

### The initial morphism `ℤ → (X,e)` preserves addition
