# Inequality of natural numbers

```agda
module elementary-number-theory.inequality-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.functions
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.posets
```

</details>

## Idea

The relation `≤` on the natural numbers is the unique relation such that `0` is less than any natural number, and such that `m+1 ≤ n+1` is equivalent to `m ≤ n`.

## Definitions

### The partial ordering on ℕ

```agda
leq-ℕ : ℕ → ℕ → UU lzero
leq-ℕ zero-ℕ m = unit
leq-ℕ (succ-ℕ n) zero-ℕ = empty
leq-ℕ (succ-ℕ n) (succ-ℕ m) = leq-ℕ n m

_≤-ℕ_ = leq-ℕ
```

### Alternative definition of the partial ordering on ℕ

```agda
data leq-ℕ' : ℕ → ℕ → UU lzero where
  refl-leq-ℕ' : (n : ℕ) → leq-ℕ' n n
  propagate-leq-ℕ' : {x y z : ℕ} → succ-ℕ y ＝ z → (leq-ℕ' x y) → (leq-ℕ' x z)
```

### The strict ordering of the natural numbers

```agda
le-ℕ : ℕ → ℕ → UU lzero
le-ℕ m zero-ℕ = empty
le-ℕ zero-ℕ (succ-ℕ m) = unit
le-ℕ (succ-ℕ n) (succ-ℕ m) = le-ℕ n m

_<_ = le-ℕ
```

## Properties of `≤`

### Zero is less than or equal to any natural number

```agda
leq-zero-ℕ :
  (n : ℕ) → zero-ℕ ≤-ℕ n
leq-zero-ℕ n = star
```

### Any natural number less than zero is zero

```agda
is-zero-leq-zero-ℕ :
  (x : ℕ) → x ≤-ℕ zero-ℕ → is-zero-ℕ x
is-zero-leq-zero-ℕ zero-ℕ star = refl

is-zero-leq-zero-ℕ' :
  (x : ℕ) → x ≤-ℕ zero-ℕ → is-zero-ℕ' x
is-zero-leq-zero-ℕ' zero-ℕ star = refl
```

### Any natural number is less than or equal to its own successor

```agda
succ-leq-ℕ : (n : ℕ) → n ≤-ℕ (succ-ℕ n)
succ-leq-ℕ zero-ℕ = star
succ-leq-ℕ (succ-ℕ n) = succ-leq-ℕ n
```

### The partial ordering on ℕ is a congruence

```agda
concatenate-eq-leq-eq-ℕ :
  {x' x y y' : ℕ} → x' ＝ x → x ≤-ℕ y → y ＝ y' → x' ≤-ℕ y'
concatenate-eq-leq-eq-ℕ refl H refl = H

concatenate-leq-eq-ℕ :
  (m : ℕ) {n n' : ℕ} → m ≤-ℕ n → n ＝ n' → m ≤-ℕ n'
concatenate-leq-eq-ℕ m H refl = H

concatenate-eq-leq-ℕ :
  {m m' : ℕ} (n : ℕ) → m' ＝ m → m ≤-ℕ n → m' ≤-ℕ n
concatenate-eq-leq-ℕ n refl H = H
```

### The partial ordering on the natural numbers is decidable

```agda
is-decidable-leq-ℕ :
  (m n : ℕ) → is-decidable (leq-ℕ m n)
is-decidable-leq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-leq-ℕ zero-ℕ (succ-ℕ n) = inl star
is-decidable-leq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-leq-ℕ m n
```

### An natural number less than `n+1` is either less than `n` or it is `n+1`

```agda
decide-leq-succ-ℕ :
  (m n : ℕ) → m ≤-ℕ (succ-ℕ n) → (m ≤-ℕ n) + (m ＝ succ-ℕ n)
decide-leq-succ-ℕ zero-ℕ zero-ℕ l = inl star
decide-leq-succ-ℕ zero-ℕ (succ-ℕ n) l = inl star
decide-leq-succ-ℕ (succ-ℕ m) zero-ℕ l =
  inr (ap succ-ℕ (is-zero-leq-zero-ℕ m l))
decide-leq-succ-ℕ (succ-ℕ m) (succ-ℕ n) l =
  map-coprod id (ap succ-ℕ) (decide-leq-succ-ℕ m n l)
```

### The less than or equal to relation is a preordering

#### Inequality on ℕ is a proposition

```agda
is-prop-leq-ℕ :
  (m n : ℕ) → is-prop (leq-ℕ m n)
is-prop-leq-ℕ zero-ℕ zero-ℕ = is-prop-unit
is-prop-leq-ℕ zero-ℕ (succ-ℕ n) = is-prop-unit
is-prop-leq-ℕ (succ-ℕ m) zero-ℕ = is-prop-empty
is-prop-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-prop-leq-ℕ m n

leq-ℕ-Prop : ℕ → ℕ → Prop lzero
pr1 (leq-ℕ-Prop m n) = leq-ℕ m n
pr2 (leq-ℕ-Prop m n) = is-prop-leq-ℕ m n
```

#### Reflexivity

```agda
refl-leq-ℕ : (n : ℕ) → n ≤-ℕ n
refl-leq-ℕ zero-ℕ = star
refl-leq-ℕ (succ-ℕ n) = refl-leq-ℕ n

leq-eq-ℕ : (m n : ℕ) → m ＝ n → m ≤-ℕ n
leq-eq-ℕ m .m refl = refl-leq-ℕ m
```

#### Transitivity

```agda
transitive-leq-ℕ :
  (n m l : ℕ) → (m ≤-ℕ l) → (n ≤-ℕ m) → (n ≤-ℕ l)
transitive-leq-ℕ zero-ℕ m l p q = star
transitive-leq-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-leq-ℕ n m l p q
```

#### Antisymmetry

```agda
antisymmetric-leq-ℕ : (m n : ℕ) → m ≤-ℕ n → n ≤-ℕ m → m ＝ n
antisymmetric-leq-ℕ zero-ℕ zero-ℕ p q = refl
antisymmetric-leq-ℕ (succ-ℕ m) (succ-ℕ n) p q =
  ap succ-ℕ (antisymmetric-leq-ℕ m n p q)
```

#### The poset of natural numbers

```agda
ℕ-Poset : Poset lzero lzero
pr1 ℕ-Poset = ℕ
pr1 (pr2 ℕ-Poset) = leq-ℕ-Prop
pr1 (pr1 (pr2 (pr2 ℕ-Poset))) = refl-leq-ℕ
pr2 (pr1 (pr2 (pr2 ℕ-Poset))) = transitive-leq-ℕ
pr2 (pr2 (pr2 ℕ-Poset)) = antisymmetric-leq-ℕ
```

### For any two natural numbers we can decide which one is less than the other

```agda
decide-leq-ℕ :
  (m n : ℕ) → (m ≤-ℕ n) + (n ≤-ℕ m)
decide-leq-ℕ zero-ℕ zero-ℕ = inl star
decide-leq-ℕ zero-ℕ (succ-ℕ n) = inl star
decide-leq-ℕ (succ-ℕ m) zero-ℕ = inr star
decide-leq-ℕ (succ-ℕ m) (succ-ℕ n) = decide-leq-ℕ m n
```

### If `m` is less than `n`, then it is less than `n+1`

```agda
preserves-leq-succ-ℕ :
  (m n : ℕ) → m ≤-ℕ n → m ≤-ℕ (succ-ℕ n)
preserves-leq-succ-ℕ m n p = transitive-leq-ℕ m n (succ-ℕ n) (succ-leq-ℕ n) p
```

### Addition preserves the ordering on ℕ

```agda
preserves-order-add-ℕ :
  (k m n : ℕ) → m ≤-ℕ n → (add-ℕ m k) ≤-ℕ (add-ℕ n k)
preserves-order-add-ℕ zero-ℕ m n = id
preserves-order-add-ℕ (succ-ℕ k) m n = preserves-order-add-ℕ k m n
```

### Addition reflects the ordering on ℕ

```agda
reflects-order-add-ℕ :
  (k m n : ℕ) → (add-ℕ m k) ≤-ℕ (add-ℕ n k) → m ≤-ℕ n
reflects-order-add-ℕ zero-ℕ m n = id
reflects-order-add-ℕ (succ-ℕ k) m n = reflects-order-add-ℕ k m n
```

### Multiplication preserves the ordering on ℕ

```
preserves-order-mul-ℕ :
  (k m n : ℕ) → m ≤-ℕ n → (mul-ℕ m k) ≤-ℕ (mul-ℕ n k)
preserves-order-mul-ℕ k zero-ℕ n p = star
preserves-order-mul-ℕ k (succ-ℕ m) (succ-ℕ n) p =
  preserves-order-add-ℕ k
    ( mul-ℕ m k)
    ( mul-ℕ n k)
    ( preserves-order-mul-ℕ k m n p)

preserves-order-mul-ℕ' :
  (k m n : ℕ) → m ≤-ℕ n → (mul-ℕ k m) ≤-ℕ (mul-ℕ k n)
preserves-order-mul-ℕ' k m n H =
  concatenate-eq-leq-eq-ℕ
    ( commutative-mul-ℕ k m)
    ( preserves-order-mul-ℕ k m n H)
    ( commutative-mul-ℕ n k)
```

### Multiplication by a nonzero element reflects the ordering on ℕ

```agda
reflects-order-mul-ℕ :
  (k m n : ℕ) → (mul-ℕ m (succ-ℕ k)) ≤-ℕ (mul-ℕ n (succ-ℕ k)) → m ≤-ℕ n
reflects-order-mul-ℕ k zero-ℕ n p = star
reflects-order-mul-ℕ k (succ-ℕ m) (succ-ℕ n) p =
  reflects-order-mul-ℕ k m n
    ( reflects-order-add-ℕ
      ( succ-ℕ k)
      ( mul-ℕ m (succ-ℕ k))
      ( mul-ℕ n (succ-ℕ k))
      ( p))
```

### Any number `x` is less than a nonzero multiple of itself

```agda
leq-mul-ℕ :
  (k x : ℕ) → x ≤-ℕ (mul-ℕ x (succ-ℕ k))
leq-mul-ℕ k x =
  concatenate-eq-leq-ℕ
    ( mul-ℕ x (succ-ℕ k))
    ( inv (right-unit-law-mul-ℕ x))
    ( preserves-order-mul-ℕ' x 1 (succ-ℕ k) (leq-zero-ℕ k))

leq-mul-ℕ' :
  (k x : ℕ) → x ≤-ℕ (mul-ℕ (succ-ℕ k) x)
leq-mul-ℕ' k x =
  concatenate-leq-eq-ℕ x
    ( leq-mul-ℕ k x)
    ( commutative-mul-ℕ x (succ-ℕ k))

leq-mul-is-nonzero-ℕ :
  (k x : ℕ) → is-nonzero-ℕ k → x ≤-ℕ (mul-ℕ x k)
leq-mul-is-nonzero-ℕ k x H with is-successor-is-nonzero-ℕ H
... | pair l refl = leq-mul-ℕ l x

leq-mul-is-nonzero-ℕ' :
  (k x : ℕ) → is-nonzero-ℕ k → x ≤-ℕ (mul-ℕ k x)
leq-mul-is-nonzero-ℕ' k x H with is-successor-is-nonzero-ℕ H
... | pair l refl = leq-mul-ℕ' l x
```

### We have `n ≤ m` if and only if there is a number `l` such that `l+n=m`

```agda
subtraction-leq-ℕ : (n m : ℕ) → n ≤-ℕ m → Σ ℕ (λ l → add-ℕ l n ＝ m)
subtraction-leq-ℕ zero-ℕ m p = pair m refl
subtraction-leq-ℕ (succ-ℕ n) (succ-ℕ m) p = pair (pr1 P) (ap succ-ℕ (pr2 P))
  where
  P : Σ ℕ (λ l' → add-ℕ l' n ＝ m)
  P = subtraction-leq-ℕ n m p

leq-subtraction-ℕ : (n m l : ℕ) → add-ℕ l n ＝ m → n ≤-ℕ m
leq-subtraction-ℕ zero-ℕ m l p = leq-zero-ℕ m
leq-subtraction-ℕ (succ-ℕ n) (succ-ℕ m) l p = leq-subtraction-ℕ n m l (is-injective-succ-ℕ p)
```

### For any three natural numbers, there are three cases in how they can be ordered

```agda
cases-order-three-elements-ℕ :
  (x y z : ℕ) → UU lzero
cases-order-three-elements-ℕ x y z =
  ( ( leq-ℕ x y × leq-ℕ y z) +
    ( leq-ℕ x z × leq-ℕ z y)) +
  ( ( ( leq-ℕ y z × leq-ℕ z x) +
      ( leq-ℕ y x × leq-ℕ x z)) +
    ( ( leq-ℕ z x × leq-ℕ x y) +
      ( leq-ℕ z y × leq-ℕ y x)))

order-three-elements-ℕ :
  (x y z : ℕ) → cases-order-three-elements-ℕ x y z
order-three-elements-ℕ zero-ℕ zero-ℕ zero-ℕ = inl (inl (pair star star))
order-three-elements-ℕ zero-ℕ zero-ℕ (succ-ℕ z) = inl (inl (pair star star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) zero-ℕ = inl (inr (pair star star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) =
  inl (map-coprod (pair star) (pair star) (decide-leq-ℕ y z))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ zero-ℕ =
  inr (inl (inl (pair star star)))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ (succ-ℕ z) =
  inr (inl (map-coprod (pair star) (pair star) (decide-leq-ℕ z x)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) zero-ℕ =
  inr (inr (map-coprod (pair star) (pair star) (decide-leq-ℕ x y)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) =
  order-three-elements-ℕ x y z
```

## Properties of `<`

### Any natural number is strictly less than its successor

```agda
succ-le-ℕ : (n : ℕ) → le-ℕ n (succ-ℕ n)
succ-le-ℕ zero-ℕ = star
succ-le-ℕ (succ-ℕ n) = succ-le-ℕ n
```

### If `m < n` then `n` must be nonzero

```agda
is-nonzero-le-ℕ : (m n : ℕ) → le-ℕ m n → is-nonzero-ℕ n
is-nonzero-le-ℕ m .zero-ℕ () refl
```

### No natural number is strictly less than zero

```agda
contradiction-le-zero-ℕ :
  (m : ℕ) → (le-ℕ m zero-ℕ) → empty
contradiction-le-zero-ℕ zero-ℕ ()
contradiction-le-zero-ℕ (succ-ℕ m) ()
```

### No successor is strictly less than one

```agda
contradiction-le-one-ℕ :
  (n : ℕ) → le-ℕ (succ-ℕ n) 1 → empty
contradiction-le-one-ℕ zero-ℕ ()
contradiction-le-one-ℕ (succ-ℕ n) ()
```

### The strict ordering of the natural numbers is anti-reflexive

```agda
anti-reflexive-le-ℕ : (n : ℕ) → ¬ (n < n)
anti-reflexive-le-ℕ zero-ℕ ()
anti-reflexive-le-ℕ (succ-ℕ n) = anti-reflexive-le-ℕ n
```

### Strict inequality is antisymmetric

```agda
anti-symmetric-le-ℕ : (m n : ℕ) → le-ℕ m n → le-ℕ n m → m ＝ n
anti-symmetric-le-ℕ (succ-ℕ m) (succ-ℕ n) p q =
  ap succ-ℕ (anti-symmetric-le-ℕ m n p q)
```

### The strict ordering of the natural numbers is transitive

```agda
transitive-le-ℕ : (n m l : ℕ) → (le-ℕ n m) → (le-ℕ m l) → (le-ℕ n l)
transitive-le-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ l) p q = star
transitive-le-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-le-ℕ n m l p q
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

### The successor function preserves strict inequality on the right

```agda
preserves-le-succ-ℕ :
  (m n : ℕ) → le-ℕ m n → le-ℕ m (succ-ℕ n)
preserves-le-succ-ℕ m n H =
  transitive-le-ℕ m n (succ-ℕ n) H (succ-le-ℕ n)
```

### Strict inequality is decidable

```agda
is-decidable-le-ℕ :
  (m n : ℕ) → is-decidable (le-ℕ m n)
is-decidable-le-ℕ zero-ℕ zero-ℕ = inr id
is-decidable-le-ℕ zero-ℕ (succ-ℕ n) = inl star
is-decidable-le-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-le-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-le-ℕ m n
```

## Properties relating nonstrict and strict inequality

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

```agda
contradiction-leq-ℕ : (m n : ℕ) → m ≤-ℕ n → ¬ ((succ-ℕ n) ≤-ℕ m)
contradiction-leq-ℕ (succ-ℕ m) (succ-ℕ n) H K = contradiction-leq-ℕ m n H K

contradiction-leq-ℕ' : (m n : ℕ) → (succ-ℕ n) ≤-ℕ m → ¬ (m ≤-ℕ n)
contradiction-leq-ℕ' m n K H = contradiction-leq-ℕ m n H K

leq-le-ℕ :
  {x y : ℕ} → le-ℕ x y → x ≤-ℕ y
leq-le-ℕ {zero-ℕ} {succ-ℕ y} H = star
leq-le-ℕ {succ-ℕ x} {succ-ℕ y} H = leq-le-ℕ {x} {y} H

leq-le-succ-ℕ :
  {x y : ℕ} → le-ℕ x (succ-ℕ y) → x ≤-ℕ y
leq-le-succ-ℕ {zero-ℕ} {y} H = star
leq-le-succ-ℕ {succ-ℕ x} {succ-ℕ y} H = leq-le-succ-ℕ {x} {y} H

leq-succ-le-ℕ :
  (x y : ℕ) → le-ℕ x y → leq-ℕ (succ-ℕ x) y
leq-succ-le-ℕ zero-ℕ (succ-ℕ y) H = star
leq-succ-le-ℕ (succ-ℕ x) (succ-ℕ y) H = leq-succ-le-ℕ x y H

concatenate-leq-le-ℕ :
  {x y z : ℕ} → x ≤-ℕ y → le-ℕ y z → le-ℕ x z
concatenate-leq-le-ℕ {zero-ℕ} {zero-ℕ} {succ-ℕ z} H K = star
concatenate-leq-le-ℕ {zero-ℕ} {succ-ℕ y} {succ-ℕ z} H K = star
concatenate-leq-le-ℕ {succ-ℕ x} {succ-ℕ y} {succ-ℕ z} H K =
  concatenate-leq-le-ℕ {x} {y} {z} H K

concatenate-le-leq-ℕ :
  {x y z : ℕ} → le-ℕ x y → y ≤-ℕ z → le-ℕ x z
concatenate-le-leq-ℕ {zero-ℕ} {succ-ℕ y} {succ-ℕ z} H K = star
concatenate-le-leq-ℕ {succ-ℕ x} {succ-ℕ y} {succ-ℕ z} H K =
  concatenate-le-leq-ℕ {x} {y} {z} H K

concatenate-eq-le-eq-ℕ :
  {x y z w : ℕ} → x ＝ y → le-ℕ y z → z ＝ w → le-ℕ x w
concatenate-eq-le-eq-ℕ refl p refl = p

concatenate-eq-le-ℕ :
  {x y z : ℕ} → x ＝ y → le-ℕ y z → le-ℕ x z
concatenate-eq-le-ℕ refl p = p

concatenate-le-eq-ℕ :
  {x y z : ℕ} → le-ℕ x y → y ＝ z → le-ℕ x z
concatenate-le-eq-ℕ p refl = p

le-succ-ℕ : {x : ℕ} → le-ℕ x (succ-ℕ x)
le-succ-ℕ {zero-ℕ} = star
le-succ-ℕ {succ-ℕ x} = le-succ-ℕ {x}

le-leq-neq-ℕ : {x y : ℕ} → x ≤-ℕ y → ¬ (x ＝ y) → le-ℕ x y
le-leq-neq-ℕ {zero-ℕ} {zero-ℕ} l f = ex-falso (f refl)
le-leq-neq-ℕ {zero-ℕ} {succ-ℕ y} l f = star
le-leq-neq-ℕ {succ-ℕ x} {succ-ℕ y} l f =
  le-leq-neq-ℕ {x} {y} l (λ p → f (ap succ-ℕ p))

linear-le-ℕ : (x y : ℕ) → (le-ℕ x y) + ((x ＝ y) + (le-ℕ y x))
linear-le-ℕ zero-ℕ zero-ℕ = inr (inl refl)
linear-le-ℕ zero-ℕ (succ-ℕ y) = inl star
linear-le-ℕ (succ-ℕ x) zero-ℕ = inr (inr star)
linear-le-ℕ (succ-ℕ x) (succ-ℕ y) =
  map-coprod id (map-coprod (ap succ-ℕ) id) (linear-le-ℕ x y)

le-is-nonzero-ℕ : (n : ℕ) → is-nonzero-ℕ n → le-ℕ zero-ℕ n
le-is-nonzero-ℕ zero-ℕ H = H refl
le-is-nonzero-ℕ (succ-ℕ n) H = concatenate-leq-le-ℕ {x = zero-ℕ} {y = n} {z = succ-ℕ n} (leq-zero-ℕ n) (succ-le-ℕ n)

subtraction-le-ℕ :
  (n m : ℕ) → le-ℕ n m → Σ ℕ (λ l → (is-nonzero-ℕ l) × (add-ℕ l n ＝ m))
subtraction-le-ℕ zero-ℕ m p = pair m (pair (is-nonzero-le-ℕ zero-ℕ m p) refl)
subtraction-le-ℕ (succ-ℕ n) (succ-ℕ m) p = pair (pr1 P) (pair (pr1 (pr2 P)) (ap succ-ℕ (pr2 (pr2 P))))
  where
  P : Σ ℕ (λ l' → (is-nonzero-ℕ l') × (add-ℕ l' n ＝ m))
  P = subtraction-le-ℕ n m p

le-subtraction-ℕ : (n m l : ℕ) → is-nonzero-ℕ l → add-ℕ l n ＝ m → le-ℕ n m
le-subtraction-ℕ zero-ℕ m l q p = tr (λ x → le-ℕ zero-ℕ x) p (le-is-nonzero-ℕ l q)
le-subtraction-ℕ (succ-ℕ n) (succ-ℕ m) l q p = le-subtraction-ℕ n m l q (is-injective-succ-ℕ p)
```

```agda
left-law-leq-add-ℕ : (k m n : ℕ) → m ≤-ℕ n → (add-ℕ m k) ≤-ℕ (add-ℕ n k)
left-law-leq-add-ℕ zero-ℕ m n = id
left-law-leq-add-ℕ (succ-ℕ k) m n H = left-law-leq-add-ℕ k m n H

right-law-leq-add-ℕ : (k m n : ℕ) → m ≤-ℕ n → (add-ℕ k m) ≤-ℕ (add-ℕ k n)
right-law-leq-add-ℕ k m n H =
  concatenate-eq-leq-eq-ℕ
    ( commutative-add-ℕ k m)
    ( left-law-leq-add-ℕ k m n H)
    ( commutative-add-ℕ n k)

preserves-leq-add-ℕ :
  {m m' n n' : ℕ} → m ≤-ℕ m' → n ≤-ℕ n' → (add-ℕ m n) ≤-ℕ (add-ℕ m' n')
preserves-leq-add-ℕ {m} {m'} {n} {n'} H K =
  transitive-leq-ℕ
    ( add-ℕ m n)
    ( add-ℕ m' n)
    ( add-ℕ m' n')
    ( right-law-leq-add-ℕ m' n n' K)
    ( left-law-leq-add-ℕ n m m' H)

--------------------------------------------------------------------------------

-- We prove some lemmas about inequalities --

leq-add-ℕ : (m n : ℕ) → m ≤-ℕ (add-ℕ m n)
leq-add-ℕ m zero-ℕ = refl-leq-ℕ m
leq-add-ℕ m (succ-ℕ n) =
  transitive-leq-ℕ m (add-ℕ m n) (succ-ℕ (add-ℕ m n))
    ( succ-leq-ℕ (add-ℕ m n))
    ( leq-add-ℕ m n)

leq-add-ℕ' : (m n : ℕ) → m ≤-ℕ (add-ℕ n m)
leq-add-ℕ' m n =
  concatenate-leq-eq-ℕ m (leq-add-ℕ m n) (commutative-add-ℕ m n)

leq-leq-add-ℕ :
  (m n x : ℕ) → (add-ℕ m x) ≤-ℕ (add-ℕ n x) → m ≤-ℕ n
leq-leq-add-ℕ m n zero-ℕ H = H
leq-leq-add-ℕ m n (succ-ℕ x) H = leq-leq-add-ℕ m n x H

leq-leq-add-ℕ' :
  (m n x : ℕ) → (add-ℕ x m) ≤-ℕ (add-ℕ x n) → m ≤-ℕ n
leq-leq-add-ℕ' m n x H =
  leq-leq-add-ℕ m n x
    ( concatenate-eq-leq-eq-ℕ
      ( commutative-add-ℕ m x)
      ( H)
      ( commutative-add-ℕ x n))

leq-leq-mul-ℕ :
  (m n x : ℕ) → (mul-ℕ (succ-ℕ x) m) ≤-ℕ (mul-ℕ (succ-ℕ x) n) → m ≤-ℕ n
leq-leq-mul-ℕ zero-ℕ zero-ℕ x H = star
leq-leq-mul-ℕ zero-ℕ (succ-ℕ n) x H = star
leq-leq-mul-ℕ (succ-ℕ m) zero-ℕ x H =
  ex-falso
    ( concatenate-leq-eq-ℕ
      ( mul-ℕ (succ-ℕ x) (succ-ℕ m))
      ( H)
      ( right-zero-law-mul-ℕ (succ-ℕ x)))
leq-leq-mul-ℕ (succ-ℕ m) (succ-ℕ n) x H =
  leq-leq-mul-ℕ m n x
    ( leq-leq-add-ℕ' (mul-ℕ (succ-ℕ x) m) (mul-ℕ (succ-ℕ x) n) (succ-ℕ x)
      ( concatenate-eq-leq-eq-ℕ
        ( inv (right-successor-law-mul-ℕ (succ-ℕ x) m))
        ( H)
        ( right-successor-law-mul-ℕ (succ-ℕ x) n)))

leq-leq-mul-ℕ' :
  (m n x : ℕ) → (mul-ℕ m (succ-ℕ x)) ≤-ℕ (mul-ℕ n (succ-ℕ x)) → m ≤-ℕ n
leq-leq-mul-ℕ' m n x H =
  leq-leq-mul-ℕ m n x
    ( concatenate-eq-leq-eq-ℕ
      ( commutative-mul-ℕ (succ-ℕ x) m)
      ( H)
      ( commutative-mul-ℕ n (succ-ℕ x)))
```

```agda
neq-le-ℕ : {x y : ℕ} → le-ℕ x y → ¬ (x ＝ y)
neq-le-ℕ {zero-ℕ} {succ-ℕ y} H = is-nonzero-succ-ℕ y ∘ inv
neq-le-ℕ {succ-ℕ x} {succ-ℕ y} H p = neq-le-ℕ H (is-injective-succ-ℕ p)
```

```agda
neg-succ-leq-ℕ :
  (n : ℕ) → ¬ (leq-ℕ (succ-ℕ n) n)
neg-succ-leq-ℕ zero-ℕ = id
neg-succ-leq-ℕ (succ-ℕ n) = neg-succ-leq-ℕ n

leq-eq-left-ℕ :
  {m m' : ℕ} → m ＝ m' → (n : ℕ) → leq-ℕ m n → leq-ℕ m' n
leq-eq-left-ℕ refl n = id

leq-eq-right-ℕ :
  (m : ℕ) {n n' : ℕ} → n ＝ n' → leq-ℕ m n → leq-ℕ m n'
leq-eq-right-ℕ m refl = id

cases-leq-succ-ℕ :
  {m n : ℕ} → leq-ℕ m (succ-ℕ n) → (leq-ℕ m n) + (m ＝ succ-ℕ n)
cases-leq-succ-ℕ {zero-ℕ} {n} star = inl star
cases-leq-succ-ℕ {succ-ℕ m} {zero-ℕ} p =
  inr (ap succ-ℕ (antisymmetric-leq-ℕ m zero-ℕ p star))
cases-leq-succ-ℕ {succ-ℕ m} {succ-ℕ n} p =
  map-coprod id (ap succ-ℕ) (cases-leq-succ-ℕ p)
```
