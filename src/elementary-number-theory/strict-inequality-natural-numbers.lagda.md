# Strict inequality on the natural numbers

```agda
module elementary-number-theory.strict-inequality-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Definition

### The standard strict inequality on the natural numbers

```agda
le-ℕ-Prop : ℕ → ℕ → Prop lzero
le-ℕ-Prop m zero-ℕ = empty-Prop
le-ℕ-Prop zero-ℕ (succ-ℕ m) = unit-Prop
le-ℕ-Prop (succ-ℕ n) (succ-ℕ m) = le-ℕ-Prop n m

le-ℕ : ℕ → ℕ → UU lzero
le-ℕ n m = type-Prop (le-ℕ-Prop n m)

is-prop-le-ℕ : (n : ℕ) → (m : ℕ) → is-prop (le-ℕ n m)
is-prop-le-ℕ n m = is-prop-type-Prop (le-ℕ-Prop n m)

infix 30 _<-ℕ_
_<-ℕ_ = le-ℕ
```

## Properties

### Concatenating strict inequalities and equalities

```agda
concatenate-eq-le-eq-ℕ :
  (x y z w : ℕ) → x ＝ y → le-ℕ y z → z ＝ w → le-ℕ x w
concatenate-eq-le-eq-ℕ x y z .z refl p refl = p

concatenate-eq-le-ℕ :
  (x y z : ℕ) → x ＝ y → le-ℕ y z → le-ℕ x z
concatenate-eq-le-ℕ x .x z refl p = p

concatenate-le-eq-ℕ :
  (x y z : ℕ) → le-ℕ x y → y ＝ z → le-ℕ x z
concatenate-le-eq-ℕ x y .y p refl = p
```

### Strict inequality on the natural numbers is decidable

```agda
is-decidable-le-ℕ :
  (m n : ℕ) → is-decidable (le-ℕ m n)
is-decidable-le-ℕ zero-ℕ zero-ℕ = inr id
is-decidable-le-ℕ zero-ℕ (succ-ℕ n) = inl star
is-decidable-le-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-le-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-le-ℕ m n
```

### If `m < n` then `n` must be nonzero

```agda
is-nonzero-le-ℕ : (m n : ℕ) → le-ℕ m n → is-nonzero-ℕ n
is-nonzero-le-ℕ m .zero-ℕ () refl
```

### Any nonzero natural number is strictly greater than `0`

```agda
le-zero-is-nonzero-ℕ : (n : ℕ) → is-nonzero-ℕ n → le-ℕ zero-ℕ n
le-zero-is-nonzero-ℕ zero-ℕ H = H refl
le-zero-is-nonzero-ℕ (succ-ℕ n) H = star
```

### No natural number is strictly less than zero

```agda
contradiction-le-zero-ℕ :
  (m : ℕ) → (le-ℕ m zero-ℕ) → empty
contradiction-le-zero-ℕ zero-ℕ ()
contradiction-le-zero-ℕ (succ-ℕ m) ()
```

### Any natural number strictly greater than another natural number is strictly greater than `0`

```agda
le-zero-le-ℕ :
  (m n : ℕ) → m <-ℕ n → 0 <-ℕ n
le-zero-le-ℕ m (succ-ℕ n) H = star
```

### No successor is strictly less than one

```agda
contradiction-le-one-ℕ :
  (n : ℕ) → le-ℕ (succ-ℕ n) 1 → empty
contradiction-le-one-ℕ zero-ℕ ()
contradiction-le-one-ℕ (succ-ℕ n) ()
```

### The strict inequality on the natural numbers is anti-reflexive

```agda
anti-reflexive-le-ℕ : (n : ℕ) → ¬ (n <-ℕ n)
anti-reflexive-le-ℕ zero-ℕ ()
anti-reflexive-le-ℕ (succ-ℕ n) = anti-reflexive-le-ℕ n
```

### If `x < y` then `x ≠ y`

```agda
neq-le-ℕ : {x y : ℕ} → le-ℕ x y → x ≠ y
neq-le-ℕ {zero-ℕ} {succ-ℕ y} H = is-nonzero-succ-ℕ y ∘ inv
neq-le-ℕ {succ-ℕ x} {succ-ℕ y} H p = neq-le-ℕ H (is-injective-succ-ℕ p)
```

### The strict inequality on the natural numbers is antisymmetric

```agda
antisymmetric-le-ℕ : (m n : ℕ) → le-ℕ m n → le-ℕ n m → m ＝ n
antisymmetric-le-ℕ (succ-ℕ m) (succ-ℕ n) p q =
  ap succ-ℕ (antisymmetric-le-ℕ m n p q)
```

### The strict inequality on the natural numbers is transitive

```agda
transitive-le-ℕ : (n m l : ℕ) → (le-ℕ n m) → (le-ℕ m l) → (le-ℕ n l)
transitive-le-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ l) p q = star
transitive-le-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-le-ℕ n m l p q

concatenate-le-eq-le-ℕ :
  (a b c d : ℕ) → a <-ℕ b → b ＝ c → c <-ℕ d → a <-ℕ d
concatenate-le-eq-le-ℕ a b .b d H refl K =
  transitive-le-ℕ a b d H K
```

### A sharper variant of transitivity

```agda
transitive-le-ℕ' :
  (k l m : ℕ) → (le-ℕ k l) → (le-ℕ l (succ-ℕ m)) → le-ℕ k m
transitive-le-ℕ' zero-ℕ zero-ℕ m () s
transitive-le-ℕ' (succ-ℕ k) zero-ℕ m () s
transitive-le-ℕ' zero-ℕ (succ-ℕ l) zero-ℕ star s =
  ex-falso (contradiction-le-one-ℕ l s)
transitive-le-ℕ' (succ-ℕ k) (succ-ℕ l) zero-ℕ t s =
  ex-falso (contradiction-le-one-ℕ l s)
transitive-le-ℕ' zero-ℕ (succ-ℕ l) (succ-ℕ m) star s = star
transitive-le-ℕ' (succ-ℕ k) (succ-ℕ l) (succ-ℕ m) t s =
  transitive-le-ℕ' k l m t s
```

### The strict inequality on the natural numbers is linear

```agda
linear-le-ℕ : (x y : ℕ) → (le-ℕ x y) + ((x ＝ y) + (le-ℕ y x))
linear-le-ℕ zero-ℕ zero-ℕ = inr (inl refl)
linear-le-ℕ zero-ℕ (succ-ℕ y) = inl star
linear-le-ℕ (succ-ℕ x) zero-ℕ = inr (inr star)
linear-le-ℕ (succ-ℕ x) (succ-ℕ y) =
  map-coproduct id (map-coproduct (ap succ-ℕ) id) (linear-le-ℕ x y)
```

### `n < m` if and only if there exists a nonzero natural number `l` such that `n + l = m`

```agda
subtraction-le-ℕ :
  (n m : ℕ) → le-ℕ n m → Σ ℕ (λ l → (is-nonzero-ℕ l) × (l +ℕ n ＝ m))
subtraction-le-ℕ zero-ℕ m p = pair m (pair (is-nonzero-le-ℕ zero-ℕ m p) refl)
subtraction-le-ℕ (succ-ℕ n) (succ-ℕ m) p =
  pair (pr1 P) (pair (pr1 (pr2 P)) (ap succ-ℕ (pr2 (pr2 P))))
  where
  P : Σ ℕ (λ l' → (is-nonzero-ℕ l') × (l' +ℕ n ＝ m))
  P = subtraction-le-ℕ n m p

le-subtraction-ℕ : (n m l : ℕ) → is-nonzero-ℕ l → l +ℕ n ＝ m → le-ℕ n m
le-subtraction-ℕ zero-ℕ m l q p =
  tr (λ x → le-ℕ zero-ℕ x) p (le-zero-is-nonzero-ℕ l q)
le-subtraction-ℕ (succ-ℕ n) (succ-ℕ m) l q p =
  le-subtraction-ℕ n m l q (is-injective-succ-ℕ p)
```

### Any natural number is strictly less than its successor

```agda
succ-le-ℕ : (n : ℕ) → le-ℕ n (succ-ℕ n)
succ-le-ℕ zero-ℕ = star
succ-le-ℕ (succ-ℕ n) = succ-le-ℕ n
```

### The successor function preserves strict inequality on the right

```agda
preserves-le-succ-ℕ :
  (m n : ℕ) → le-ℕ m n → le-ℕ m (succ-ℕ n)
preserves-le-succ-ℕ m n H =
  transitive-le-ℕ m n (succ-ℕ n) H (succ-le-ℕ n)
```

### Concatenating strict and nonstrict inequalities

```agda
concatenate-leq-le-ℕ :
  (x y z : ℕ) → x ≤-ℕ y → le-ℕ y z → le-ℕ x z
concatenate-leq-le-ℕ zero-ℕ zero-ℕ (succ-ℕ z) H K = star
concatenate-leq-le-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) H K = star
concatenate-leq-le-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) H K =
  concatenate-leq-le-ℕ x y z H K

concatenate-le-leq-ℕ :
  (x y z : ℕ) → le-ℕ x y → y ≤-ℕ z → le-ℕ x z
concatenate-le-leq-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) H K = star
concatenate-le-leq-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) H K =
  concatenate-le-leq-ℕ x y z H K
```

### If `m < n` then `n ≰ m`

```agda
contradiction-le-ℕ : (m n : ℕ) → le-ℕ m n → ¬ (n ≤-ℕ m)
contradiction-le-ℕ zero-ℕ (succ-ℕ n) H K = K
contradiction-le-ℕ (succ-ℕ m) (succ-ℕ n) H = contradiction-le-ℕ m n H
```

### If `n ≤ m` then `m ≮ n`

```agda
contradiction-le-ℕ' : (m n : ℕ) → n ≤-ℕ m → ¬ (le-ℕ m n)
contradiction-le-ℕ' m n K H = contradiction-le-ℕ m n H K
```

### If `m ≮ n` then `n ≤ m`

```agda
leq-not-le-ℕ : (m n : ℕ) → ¬ (le-ℕ m n) → n ≤-ℕ m
leq-not-le-ℕ zero-ℕ zero-ℕ H = star
leq-not-le-ℕ zero-ℕ (succ-ℕ n) H = ex-falso (H star)
leq-not-le-ℕ (succ-ℕ m) zero-ℕ H = star
leq-not-le-ℕ (succ-ℕ m) (succ-ℕ n) H = leq-not-le-ℕ m n H
```

### If `m ≰ n` then `n < m`

```agda
le-not-leq-ℕ : (m n : ℕ) → ¬ (m ≤-ℕ n) → n <-ℕ m
le-not-leq-ℕ zero-ℕ zero-ℕ H = ex-falso (H star)
le-not-leq-ℕ zero-ℕ (succ-ℕ n) H = ex-falso (H star)
le-not-leq-ℕ (succ-ℕ m) zero-ℕ H = star
le-not-leq-ℕ (succ-ℕ m) (succ-ℕ n) H = le-not-leq-ℕ m n H
```

### If `x < y` then `x ≤ y`

```agda
leq-le-ℕ :
  (x y : ℕ) → le-ℕ x y → x ≤-ℕ y
leq-le-ℕ zero-ℕ (succ-ℕ y) H = star
leq-le-ℕ (succ-ℕ x) (succ-ℕ y) H = leq-le-ℕ x y H
```

### If `x < y + 1` then `x ≤ y`

```agda
leq-le-succ-ℕ :
  (x y : ℕ) → le-ℕ x (succ-ℕ y) → x ≤-ℕ y
leq-le-succ-ℕ zero-ℕ y H = star
leq-le-succ-ℕ (succ-ℕ x) (succ-ℕ y) H = leq-le-succ-ℕ x y H
```

### If `x < y` then `x + 1 ≤ y`

```agda
leq-succ-le-ℕ :
  (x y : ℕ) → le-ℕ x y → leq-ℕ (succ-ℕ x) y
leq-succ-le-ℕ zero-ℕ (succ-ℕ y) H = star
leq-succ-le-ℕ (succ-ℕ x) (succ-ℕ y) H = leq-succ-le-ℕ x y H
```

### If `x ≤ y` then `x < y + 1`

```agda
le-succ-leq-ℕ :
  (x y : ℕ) → leq-ℕ x y → le-ℕ x (succ-ℕ y)
le-succ-leq-ℕ zero-ℕ zero-ℕ H = star
le-succ-leq-ℕ zero-ℕ (succ-ℕ y) H = star
le-succ-leq-ℕ (succ-ℕ x) (succ-ℕ y) H = le-succ-leq-ℕ x y H
```

### `x ≤ y` if and only if `(x ＝ y) + (x < y)`

```agda
eq-or-le-leq-ℕ :
  (x y : ℕ) → leq-ℕ x y → ((x ＝ y) + (le-ℕ x y))
eq-or-le-leq-ℕ zero-ℕ zero-ℕ H = inl refl
eq-or-le-leq-ℕ zero-ℕ (succ-ℕ y) H = inr star
eq-or-le-leq-ℕ (succ-ℕ x) (succ-ℕ y) H =
  map-coproduct (ap succ-ℕ) id (eq-or-le-leq-ℕ x y H)

eq-or-le-leq-ℕ' :
  (x y : ℕ) → leq-ℕ x y → ((y ＝ x) + (le-ℕ x y))
eq-or-le-leq-ℕ' x y H = map-coproduct inv id (eq-or-le-leq-ℕ x y H)

leq-eq-or-le-ℕ :
  (x y : ℕ) → ((x ＝ y) + (le-ℕ x y)) → leq-ℕ x y
leq-eq-or-le-ℕ x .x (inl refl) = refl-leq-ℕ x
leq-eq-or-le-ℕ x y (inr l) = leq-le-ℕ x y l
```

### If `x ≤ y` and `x ≠ y` then `x < y`

```agda
le-leq-neq-ℕ : {x y : ℕ} → x ≤-ℕ y → x ≠ y → le-ℕ x y
le-leq-neq-ℕ {zero-ℕ} {zero-ℕ} l f = ex-falso (f refl)
le-leq-neq-ℕ {zero-ℕ} {succ-ℕ y} l f = star
le-leq-neq-ℕ {succ-ℕ x} {succ-ℕ y} l f =
  le-leq-neq-ℕ {x} {y} l (λ p → f (ap succ-ℕ p))
```

### `x < x + y` for any nonzero natural number `y`

```agda
le-add-succ-ℕ :
  (x y : ℕ) → x <-ℕ x +ℕ succ-ℕ y
le-add-succ-ℕ zero-ℕ y = star
le-add-succ-ℕ (succ-ℕ x) y =
  concatenate-le-eq-ℕ x
    ( x +ℕ succ-ℕ y)
    ( succ-ℕ x +ℕ y)
    ( le-add-succ-ℕ x y)
    ( inv (left-successor-law-add-ℕ x y))

le-add-ℕ :
  (x y : ℕ) → is-nonzero-ℕ y → x <-ℕ x +ℕ y
le-add-ℕ x zero-ℕ H = ex-falso (H refl)
le-add-ℕ x (succ-ℕ y) H = le-add-succ-ℕ x y
```

### If `1 < x` and `1 < y`, then `1 < xy`

```agda
le-one-mul-ℕ : (x y : ℕ) → 1 <-ℕ x → 1 <-ℕ y → 1 <-ℕ (x *ℕ y)
le-one-mul-ℕ (succ-ℕ (succ-ℕ x)) (succ-ℕ (succ-ℕ y)) star star = star
```

### Addition is strictly order preserving

```agda
preserves-strict-order-left-add-ℕ :
  (a b c : ℕ) → a <-ℕ b → a +ℕ c <-ℕ b +ℕ c
preserves-strict-order-left-add-ℕ zero-ℕ (succ-ℕ b) c H =
  concatenate-eq-le-eq-ℕ
    ( 0 +ℕ c)
    ( c)
    ( c +ℕ succ-ℕ b)
    ( succ-ℕ b +ℕ c)
    ( left-unit-law-add-ℕ c)
    ( le-add-succ-ℕ c b)
    ( commutative-add-ℕ c (succ-ℕ b))
preserves-strict-order-left-add-ℕ (succ-ℕ a) (succ-ℕ b) c H =
  concatenate-eq-le-eq-ℕ
    ( succ-ℕ a +ℕ c)
    ( succ-ℕ (a +ℕ c))
    ( succ-ℕ (b +ℕ c))
    ( succ-ℕ b +ℕ c)
    ( left-successor-law-add-ℕ a c)
    ( preserves-strict-order-left-add-ℕ a b c H)
    ( inv (left-successor-law-add-ℕ b c))

preserves-strict-order-right-add-ℕ :
  (a c d : ℕ) → c <-ℕ d → a +ℕ c <-ℕ a +ℕ d
preserves-strict-order-right-add-ℕ a c d H =
  concatenate-eq-le-eq-ℕ
    ( a +ℕ c)
    ( c +ℕ a)
    ( d +ℕ a)
    ( a +ℕ d)
    ( commutative-add-ℕ a c)
    ( preserves-strict-order-left-add-ℕ c d a H)
    ( commutative-add-ℕ d a)

preserves-strict-order-add-ℕ :
  (a b c d : ℕ) → a <-ℕ b → c <-ℕ d → a +ℕ c <-ℕ b +ℕ d
preserves-strict-order-add-ℕ a b c d H K =
  transitive-le-ℕ
    ( a +ℕ c)
    ( b +ℕ c)
    ( b +ℕ d)
    ( preserves-strict-order-left-add-ℕ a b c H)
    ( preserves-strict-order-right-add-ℕ b c d K)
```

### Multiplication is strictly order preserving

```agda
preserves-strict-order-mul-ℕ :
  (a b c d : ℕ) → a <-ℕ b → c <-ℕ d → a *ℕ c <-ℕ b *ℕ d
preserves-strict-order-mul-ℕ zero-ℕ (succ-ℕ b) zero-ℕ (succ-ℕ d) H K = star
preserves-strict-order-mul-ℕ zero-ℕ (succ-ℕ b) (succ-ℕ c) (succ-ℕ d) H K = star
preserves-strict-order-mul-ℕ (succ-ℕ a) (succ-ℕ b) zero-ℕ (succ-ℕ d) H K =
  concatenate-eq-le-ℕ
    ( a *ℕ 0)
    ( 0)
    ( succ-ℕ b *ℕ succ-ℕ d)
    ( right-zero-law-mul-ℕ a)
    ( star)
preserves-strict-order-mul-ℕ (succ-ℕ a) (succ-ℕ b) (succ-ℕ c) (succ-ℕ d) H K =
  concatenate-eq-le-eq-ℕ
    ( succ-ℕ a *ℕ succ-ℕ c)
    ( a *ℕ c +ℕ a +ℕ c +ℕ 1)
    ( b *ℕ d +ℕ b +ℕ d +ℕ 1)
    ( succ-ℕ b *ℕ succ-ℕ d)
    ( double-successor-law-mul-ℕ a c)
    ( preserves-strict-order-add-ℕ
      ( a *ℕ c +ℕ a)
      ( b *ℕ d +ℕ b)
      ( c)
      ( d)
      ( preserves-strict-order-add-ℕ
        ( a *ℕ c)
        ( b *ℕ d)
        ( a)
        ( b)
        ( preserves-strict-order-mul-ℕ a b c d H K)
        ( H))
      ( K))
    ( inv (double-successor-law-mul-ℕ b d))
```

### Multiplication by a nonzero natural number on the left or right is strictly order preserving

```agda
preserves-strict-order-left-mul-succ-ℕ :
  (k x y : ℕ) → x <-ℕ y → succ-ℕ k *ℕ x <-ℕ succ-ℕ k *ℕ y
preserves-strict-order-left-mul-succ-ℕ zero-ℕ x y H =
  concatenate-eq-le-eq-ℕ
    ( 1 *ℕ x)
    ( x)
    ( y)
    ( 1 *ℕ y)
    ( left-unit-law-mul-ℕ x)
    ( H)
    ( inv (left-unit-law-mul-ℕ y))
preserves-strict-order-left-mul-succ-ℕ (succ-ℕ k) x y H =
  concatenate-eq-le-eq-ℕ
    ( succ-ℕ (succ-ℕ k) *ℕ x)
    ( succ-ℕ k *ℕ x +ℕ x)
    ( succ-ℕ k *ℕ y +ℕ y)
    ( succ-ℕ (succ-ℕ k) *ℕ y)
    ( left-successor-law-mul-ℕ (succ-ℕ k) x)
    ( preserves-strict-order-add-ℕ
      ( succ-ℕ k *ℕ x)
      ( succ-ℕ k *ℕ y)
      ( x)
      ( y)
      ( preserves-strict-order-left-mul-succ-ℕ k x y H)
      ( H))
    ( inv (left-successor-law-mul-ℕ (succ-ℕ k) y))

preserves-strict-order-left-mul-is-successor-ℕ :
  (k x y : ℕ) → is-successor-ℕ k → x <-ℕ y → k *ℕ x <-ℕ k *ℕ y
preserves-strict-order-left-mul-is-successor-ℕ .(succ-ℕ l) x y (l , refl) =
  preserves-strict-order-left-mul-succ-ℕ l x y

preserves-strict-order-left-mul-ℕ :
  (k x y : ℕ) → is-nonzero-ℕ k → x <-ℕ y → k *ℕ x <-ℕ k *ℕ y
preserves-strict-order-left-mul-ℕ k x y H =
  preserves-strict-order-left-mul-is-successor-ℕ k x y
    ( is-successor-is-nonzero-ℕ H)

preserves-strict-order-right-mul-succ-ℕ :
  (k x y : ℕ) → x <-ℕ y → x *ℕ succ-ℕ k <-ℕ y *ℕ succ-ℕ k
preserves-strict-order-right-mul-succ-ℕ zero-ℕ x y H =
  concatenate-eq-le-eq-ℕ
    ( x *ℕ 1)
    ( x)
    ( y)
    ( y *ℕ 1)
    ( right-unit-law-mul-ℕ x)
    ( H)
    ( inv (right-unit-law-mul-ℕ y))
preserves-strict-order-right-mul-succ-ℕ (succ-ℕ k) x y H =
  concatenate-eq-le-eq-ℕ
    ( x *ℕ succ-ℕ (succ-ℕ k))
    ( x *ℕ succ-ℕ k +ℕ x)
    ( y *ℕ succ-ℕ k +ℕ y)
    ( y *ℕ succ-ℕ (succ-ℕ k))
    ( right-successor-law-mul-ℕ x (succ-ℕ k))
    ( preserves-strict-order-add-ℕ
      ( x *ℕ succ-ℕ k)
      ( y *ℕ succ-ℕ k)
      ( x)
      ( y)
      ( preserves-strict-order-right-mul-succ-ℕ k x y H)
      ( H))
    ( inv (right-successor-law-mul-ℕ y (succ-ℕ k)))

preserves-strict-order-right-mul-is-successor-ℕ :
  (k x y : ℕ) → is-successor-ℕ k → x <-ℕ y → x *ℕ k <-ℕ y *ℕ k
preserves-strict-order-right-mul-is-successor-ℕ .(succ-ℕ l) x y (l , refl) =
  preserves-strict-order-right-mul-succ-ℕ l x y

preserves-strict-order-right-mul-ℕ :
  (k x y : ℕ) → is-nonzero-ℕ k → x <-ℕ y → x *ℕ k <-ℕ y *ℕ k
preserves-strict-order-right-mul-ℕ k x y H =
  preserves-strict-order-right-mul-is-successor-ℕ k x y
    ( is-successor-is-nonzero-ℕ H)
```
