# The integers

```agda
module elementary-number-theory.integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.pointed-types-equipped-with-automorphisms
open import structured-types.types-equipped-with-endomorphisms
```

</details>

## Idea

The type of integers is an extension of the type of natural numbers including negative whole numbers.

## Definitions

### The type of integers

```agda
ℤ : UU lzero
ℤ = ℕ + (unit + ℕ)
```

### Inclusion of the negative integers

```agda
in-neg : ℕ → ℤ
in-neg n = inl n

neg-one-ℤ : ℤ
neg-one-ℤ = in-neg zero-ℕ

is-neg-one-ℤ : ℤ → UU lzero
is-neg-one-ℤ x = (x ＝ neg-one-ℤ)
```

### Zero

```agda
zero-ℤ : ℤ
zero-ℤ = inr (inl star)

is-zero-ℤ : ℤ → UU lzero
is-zero-ℤ x = (x ＝ zero-ℤ)

is-nonzero-ℤ : ℤ → UU lzero
is-nonzero-ℤ k = ¬ (is-zero-ℤ k)
```

### Inclusion of the positive integers

```agda
in-pos : ℕ → ℤ
in-pos n = inr (inr n)

one-ℤ : ℤ
one-ℤ = in-pos zero-ℕ

is-one-ℤ : ℤ → UU lzero
is-one-ℤ x = (x ＝ one-ℤ)
```

### Inclusion of the natural numbers

```agda
int-ℕ : ℕ → ℤ
int-ℕ zero-ℕ = zero-ℤ
int-ℕ (succ-ℕ n) = in-pos n

is-injective-int-ℕ : is-injective int-ℕ
is-injective-int-ℕ {zero-ℕ} {zero-ℕ} refl = refl
is-injective-int-ℕ {succ-ℕ x} {succ-ℕ y} refl = refl

is-nonzero-int-ℕ : (n : ℕ) → is-nonzero-ℕ n → is-nonzero-ℤ (int-ℕ n)
is-nonzero-int-ℕ zero-ℕ H p = H refl
```

### Induction principle on the type of integers

```agda
ind-ℤ :
  {l : Level} (P : ℤ → UU l) →
  P neg-one-ℤ → ((n : ℕ) → P (inl n) → P (inl (succ-ℕ n))) →
  P zero-ℤ →
  P one-ℤ → ((n : ℕ) → P (inr (inr (n))) → P (inr (inr (succ-ℕ n)))) →
  (k : ℤ) → P k
ind-ℤ P p-1 p-S p0 p1 pS (inl zero-ℕ) = p-1
ind-ℤ P p-1 p-S p0 p1 pS (inl (succ-ℕ x)) =
  p-S x (ind-ℤ P p-1 p-S p0 p1 pS (inl x))
ind-ℤ P p-1 p-S p0 p1 pS (inr (inl star)) = p0
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr zero-ℕ)) = p1
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr (succ-ℕ x))) =
  pS x (ind-ℤ P p-1 p-S p0 p1 pS (inr (inr (x))))
```

### The successor and predecessor functions on ℤ

```agda
succ-ℤ : ℤ → ℤ
succ-ℤ (inl zero-ℕ) = zero-ℤ
succ-ℤ (inl (succ-ℕ x)) = inl x
succ-ℤ (inr (inl star)) = one-ℤ
succ-ℤ (inr (inr x)) = inr (inr (succ-ℕ x))

pred-ℤ : ℤ → ℤ
pred-ℤ (inl x) = inl (succ-ℕ x)
pred-ℤ (inr (inl star)) = inl zero-ℕ
pred-ℤ (inr (inr zero-ℕ)) = inr (inl star)
pred-ℤ (inr (inr (succ-ℕ x))) = inr (inr x)

ℤ-Endo : Endo lzero
pr1 ℤ-Endo = ℤ
pr2 ℤ-Endo = succ-ℤ
```

### The negative of an integer

```agda
neg-ℤ : ℤ → ℤ
neg-ℤ (inl x) = inr (inr x)
neg-ℤ (inr (inl star)) = inr (inl star)
neg-ℤ (inr (inr x)) = inl x
```

## Properties

### The type of integers is a set

```agda
is-set-ℤ : is-set ℤ
is-set-ℤ = is-set-coprod is-set-ℕ (is-set-coprod is-set-unit is-set-ℕ)

ℤ-Set : Set lzero
pr1 ℤ-Set = ℤ
pr2 ℤ-Set = is-set-ℤ
```

### The successor and predecessor functions on ℤ are mutual inverses

```agda
abstract
  isretr-pred-ℤ : (pred-ℤ ∘ succ-ℤ) ~ id
  isretr-pred-ℤ (inl zero-ℕ) = refl
  isretr-pred-ℤ (inl (succ-ℕ x)) = refl
  isretr-pred-ℤ (inr (inl star)) = refl
  isretr-pred-ℤ (inr (inr zero-ℕ)) = refl
  isretr-pred-ℤ (inr (inr (succ-ℕ x))) = refl

  issec-pred-ℤ : (succ-ℤ ∘ pred-ℤ) ~ id
  issec-pred-ℤ (inl zero-ℕ) = refl
  issec-pred-ℤ (inl (succ-ℕ x)) = refl
  issec-pred-ℤ (inr (inl star)) = refl
  issec-pred-ℤ (inr (inr zero-ℕ)) = refl
  issec-pred-ℤ (inr (inr (succ-ℕ x))) = refl

abstract
  is-equiv-succ-ℤ : is-equiv succ-ℤ
  pr1 (pr1 is-equiv-succ-ℤ) = pred-ℤ
  pr2 (pr1 is-equiv-succ-ℤ) = issec-pred-ℤ
  pr1 (pr2 is-equiv-succ-ℤ) = pred-ℤ
  pr2 (pr2 is-equiv-succ-ℤ) = isretr-pred-ℤ

equiv-succ-ℤ : ℤ ≃ ℤ
pr1 equiv-succ-ℤ = succ-ℤ
pr2 equiv-succ-ℤ = is-equiv-succ-ℤ

abstract
  is-equiv-pred-ℤ : is-equiv pred-ℤ
  pr1 (pr1 is-equiv-pred-ℤ) = succ-ℤ
  pr2 (pr1 is-equiv-pred-ℤ) = isretr-pred-ℤ
  pr1 (pr2 is-equiv-pred-ℤ) = succ-ℤ
  pr2 (pr2 is-equiv-pred-ℤ) = issec-pred-ℤ

equiv-pred-ℤ : ℤ ≃ ℤ
pr1 equiv-pred-ℤ = pred-ℤ
pr2 equiv-pred-ℤ = is-equiv-pred-ℤ
```

### The successor function on ℤ is injective and has no fixed points

```agda
is-injective-succ-ℤ : is-injective succ-ℤ
is-injective-succ-ℤ {x} {y} p =
  inv (isretr-pred-ℤ x) ∙ (ap pred-ℤ p ∙ isretr-pred-ℤ y)

has-no-fixed-points-succ-ℤ : (x : ℤ) → ¬ (succ-ℤ x ＝ x)
has-no-fixed-points-succ-ℤ (inl zero-ℕ) ()
has-no-fixed-points-succ-ℤ (inl (succ-ℕ x)) ()
has-no-fixed-points-succ-ℤ (inr (inl star)) ()
```

### The negative function is an involution

```agda
neg-neg-ℤ : (neg-ℤ ∘ neg-ℤ) ~ id
neg-neg-ℤ (inl n) = refl
neg-neg-ℤ (inr (inl star)) = refl
neg-neg-ℤ (inr (inr n)) = refl

abstract
  is-equiv-neg-ℤ : is-equiv neg-ℤ
  pr1 (pr1 is-equiv-neg-ℤ) = neg-ℤ
  pr2 (pr1 is-equiv-neg-ℤ) = neg-neg-ℤ
  pr1 (pr2 is-equiv-neg-ℤ) = neg-ℤ
  pr2 (pr2 is-equiv-neg-ℤ) = neg-neg-ℤ

equiv-neg-ℤ : ℤ ≃ ℤ
pr1 equiv-neg-ℤ = neg-ℤ
pr2 equiv-neg-ℤ = is-equiv-neg-ℤ

abstract
  is-emb-neg-ℤ : is-emb neg-ℤ
  is-emb-neg-ℤ = is-emb-is-equiv is-equiv-neg-ℤ

emb-neg-ℤ : ℤ ↪ ℤ
pr1 emb-neg-ℤ = neg-ℤ
pr2 emb-neg-ℤ = is-emb-neg-ℤ

neg-pred-ℤ : (k : ℤ) → neg-ℤ (pred-ℤ k) ＝ succ-ℤ (neg-ℤ k)
neg-pred-ℤ (inl x) = refl
neg-pred-ℤ (inr (inl star)) = refl
neg-pred-ℤ (inr (inr zero-ℕ)) = refl
neg-pred-ℤ (inr (inr (succ-ℕ x))) = refl

neg-succ-ℤ : (x : ℤ) → neg-ℤ (succ-ℤ x) ＝ pred-ℤ (neg-ℤ x)
neg-succ-ℤ (inl zero-ℕ) = refl
neg-succ-ℤ (inl (succ-ℕ x)) = refl
neg-succ-ℤ (inr (inl star)) = refl
neg-succ-ℤ (inr (inr x)) = refl

pred-neg-ℤ :
  (k : ℤ) → pred-ℤ (neg-ℤ k) ＝ neg-ℤ (succ-ℤ k)
pred-neg-ℤ (inl zero-ℕ) = refl
pred-neg-ℤ (inl (succ-ℕ x)) = refl
pred-neg-ℤ (inr (inl star)) = refl
pred-neg-ℤ (inr (inr x)) = refl
```

### Nonnegative integers

```agda
is-nonnegative-ℤ : ℤ → UU lzero
is-nonnegative-ℤ (inl x) = empty
is-nonnegative-ℤ (inr k) = unit

is-nonnegative-eq-ℤ :
  {x y : ℤ} → x ＝ y → is-nonnegative-ℤ x → is-nonnegative-ℤ y
is-nonnegative-eq-ℤ refl = id

is-zero-is-nonnegative-ℤ :
  {x : ℤ} → is-nonnegative-ℤ x → is-nonnegative-ℤ (neg-ℤ x) → is-zero-ℤ x
is-zero-is-nonnegative-ℤ {inr (inl star)} H K = refl

is-nonnegative-succ-ℤ :
  (k : ℤ) → is-nonnegative-ℤ k → is-nonnegative-ℤ (succ-ℤ k)
is-nonnegative-succ-ℤ (inr (inl star)) p = star
is-nonnegative-succ-ℤ (inr (inr x)) p = star
```

### The positive integers

```agda
is-positive-ℤ : ℤ → UU lzero
is-positive-ℤ (inl x) = empty
is-positive-ℤ (inr (inl x)) = empty
is-positive-ℤ (inr (inr x)) = unit

is-prop-is-positive-ℤ : (x : ℤ) → is-prop (is-positive-ℤ x)
is-prop-is-positive-ℤ (inl x) = is-prop-empty
is-prop-is-positive-ℤ (inr (inl x)) = is-prop-empty
is-prop-is-positive-ℤ (inr (inr x)) = is-prop-unit

is-set-is-positive-ℤ : (x : ℤ) → is-set (is-positive-ℤ x)
is-set-is-positive-ℤ (inl x) = is-set-empty
is-set-is-positive-ℤ (inr (inl x)) = is-set-empty
is-set-is-positive-ℤ (inr (inr x)) = is-set-unit

is-positive-ℤ-Set : ℤ → Set lzero
is-positive-ℤ-Set z = pair (is-positive-ℤ z) (is-set-is-positive-ℤ z)

positive-ℤ : UU lzero
positive-ℤ = Σ ℤ is-positive-ℤ

is-set-positive-ℤ : is-set positive-ℤ
is-set-positive-ℤ = is-set-Σ is-set-ℤ is-set-is-positive-ℤ

positive-ℤ-Set : Set lzero
pr1 positive-ℤ-Set = positive-ℤ
pr2 positive-ℤ-Set = is-set-positive-ℤ

int-positive-ℤ : positive-ℤ → ℤ
int-positive-ℤ = pr1

-- arst : (x y : positive-ℤ) → (int-positive-ℤ x ＝ int-positive-ℤ y) → x ＝ y
-- arst (pair (inr (inr x)) is-pos-x) y p = _ -- {!ex-falso is-pos-x!}

is-positive-int-positive-ℤ :
  (x : positive-ℤ) → is-positive-ℤ (int-positive-ℤ x)
is-positive-int-positive-ℤ = pr2

is-nonnegative-is-positive-ℤ : {x : ℤ} → is-positive-ℤ x → is-nonnegative-ℤ x
is-nonnegative-is-positive-ℤ {inr (inr x)} H = H

is-nonzero-is-positive-ℤ : (x : ℤ) → is-positive-ℤ x → is-nonzero-ℤ x
is-nonzero-is-positive-ℤ (inr (inr x)) H ()

is-positive-eq-ℤ : {x y : ℤ} → x ＝ y → is-positive-ℤ x → is-positive-ℤ y
is-positive-eq-ℤ {x} refl = id

is-positive-one-ℤ : is-positive-ℤ one-ℤ
is-positive-one-ℤ = star

one-positive-ℤ : positive-ℤ
pr1 one-positive-ℤ = one-ℤ
pr2 one-positive-ℤ = is-positive-one-ℤ

is-positive-succ-ℤ : {x : ℤ} → is-nonnegative-ℤ x → is-positive-ℤ (succ-ℤ x)
is-positive-succ-ℤ {inr (inl star)} H = is-positive-one-ℤ
is-positive-succ-ℤ {inr (inr x)} H = star

is-positive-int-ℕ :
  (x : ℕ) → is-nonzero-ℕ x → is-positive-ℤ (int-ℕ x)
is-positive-int-ℕ zero-ℕ H = ex-falso (H refl)
is-positive-int-ℕ (succ-ℕ x) H = star
```

### Properties of nonnegative integers

```agda
nonnegative-ℤ : UU lzero
nonnegative-ℤ = Σ ℤ is-nonnegative-ℤ

int-nonnegative-ℤ : nonnegative-ℤ → ℤ
int-nonnegative-ℤ = pr1

is-nonnegative-int-nonnegative-ℤ :
  (x : nonnegative-ℤ) → is-nonnegative-ℤ (int-nonnegative-ℤ x)
is-nonnegative-int-nonnegative-ℤ = pr2

is-injective-int-nonnegative-ℤ : is-injective int-nonnegative-ℤ
is-injective-int-nonnegative-ℤ {pair (inr x) star} {pair (inr .x) star} refl =
  refl

is-nonnegative-int-ℕ : (n : ℕ) → is-nonnegative-ℤ (int-ℕ n)
is-nonnegative-int-ℕ zero-ℕ = star
is-nonnegative-int-ℕ (succ-ℕ n) = star

nonnegative-int-ℕ : ℕ → nonnegative-ℤ
pr1 (nonnegative-int-ℕ n) = int-ℕ n
pr2 (nonnegative-int-ℕ n) = is-nonnegative-int-ℕ n

nat-nonnegative-ℤ : nonnegative-ℤ → ℕ
nat-nonnegative-ℤ (pair (inr (inl x)) H) = zero-ℕ
nat-nonnegative-ℤ (pair (inr (inr x)) H) = succ-ℕ x

issec-nat-nonnegative-ℤ :
  (x : nonnegative-ℤ) → nonnegative-int-ℕ (nat-nonnegative-ℤ x) ＝ x
issec-nat-nonnegative-ℤ (pair (inr (inl star)) star) = refl
issec-nat-nonnegative-ℤ (pair (inr (inr x)) star) = refl

isretr-nat-nonnegative-ℤ :
  (n : ℕ) → nat-nonnegative-ℤ (nonnegative-int-ℕ n) ＝ n
isretr-nat-nonnegative-ℤ zero-ℕ = refl
isretr-nat-nonnegative-ℤ (succ-ℕ n) = refl

is-equiv-nat-nonnegative-ℤ : is-equiv nat-nonnegative-ℤ
pr1 (pr1 is-equiv-nat-nonnegative-ℤ) = nonnegative-int-ℕ
pr2 (pr1 is-equiv-nat-nonnegative-ℤ) = isretr-nat-nonnegative-ℤ
pr1 (pr2 is-equiv-nat-nonnegative-ℤ) = nonnegative-int-ℕ
pr2 (pr2 is-equiv-nat-nonnegative-ℤ) = issec-nat-nonnegative-ℤ

is-equiv-nonnegative-int-ℕ : is-equiv nonnegative-int-ℕ
pr1 (pr1 is-equiv-nonnegative-int-ℕ) = nat-nonnegative-ℤ
pr2 (pr1 is-equiv-nonnegative-int-ℕ) = issec-nat-nonnegative-ℤ
pr1 (pr2 is-equiv-nonnegative-int-ℕ) = nat-nonnegative-ℤ
pr2 (pr2 is-equiv-nonnegative-int-ℕ) = isretr-nat-nonnegative-ℤ

equiv-nonnegative-int-ℕ : ℕ ≃ nonnegative-ℤ
pr1 equiv-nonnegative-int-ℕ = nonnegative-int-ℕ
pr2 equiv-nonnegative-int-ℕ = is-equiv-nonnegative-int-ℕ

is-injective-nonnegative-int-ℕ : is-injective nonnegative-int-ℕ
is-injective-nonnegative-int-ℕ {x} {y} p =
  ( inv (isretr-nat-nonnegative-ℤ x)) ∙
  ( ( ap nat-nonnegative-ℤ p) ∙
    ( isretr-nat-nonnegative-ℤ y))

decide-is-nonnegative-ℤ :
  {x : ℤ} → (is-nonnegative-ℤ x) + (is-nonnegative-ℤ (neg-ℤ x))
decide-is-nonnegative-ℤ {inl x} = inr star
decide-is-nonnegative-ℤ {inr x} = inl star

is-zero-is-nonnegative-neg-is-nonnegative-ℤ :
  (x : ℤ) → (is-nonnegative-ℤ x) → (is-nonnegative-ℤ (neg-ℤ x)) → is-zero-ℤ x
is-zero-is-nonnegative-neg-is-nonnegative-ℤ (inr (inl star)) nonneg nonpos = refl
```

```agda
succ-int-ℕ : (x : ℕ) → succ-ℤ (int-ℕ x) ＝ int-ℕ (succ-ℕ x)
succ-int-ℕ zero-ℕ = refl
succ-int-ℕ (succ-ℕ x) = refl
```

```agda
is-injective-neg-ℤ : is-injective neg-ℤ
is-injective-neg-ℤ {x} {y} p = inv (neg-neg-ℤ x) ∙ (ap neg-ℤ p ∙ neg-neg-ℤ y)

is-zero-is-zero-neg-ℤ :
  (x : ℤ) → is-zero-ℤ (neg-ℤ x) → is-zero-ℤ x
is-zero-is-zero-neg-ℤ (inr (inl star)) H = refl
```

## See also

1. We show in [`structured-types.initial-pointed-type-equipped-with-automorphism`](structured-types.initial-pointed-type-equipped-with-automorphism.md) that ℤ is the initial pointed type equipped with an automorphism.
2. The group of integers is constructed in [`elementary-number-theory.group-of-integers`](elementary-number-theory.group-of-integers.md).
