# Strict inequality on the natural numbers

```agda
module elementary-number-theory.strict-inequality-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.strictly-preordered-sets
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
  {x y z w : ℕ} → x ＝ y → le-ℕ y z → z ＝ w → le-ℕ x w
concatenate-eq-le-eq-ℕ refl p refl = p

concatenate-eq-le-ℕ :
  {x y z : ℕ} → x ＝ y → le-ℕ y z → le-ℕ x z
concatenate-eq-le-ℕ refl p = p

concatenate-le-eq-ℕ :
  {x y z : ℕ} → le-ℕ x y → y ＝ z → le-ℕ x z
concatenate-le-eq-ℕ p refl = p
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

#### The decidable subtype of natural numbers less than `n`

For circular dependency reasons, we cannot give this the type of a decidable
subtype or proposition.

```agda
decidable-subtype-le-ℕ :
  (n m : ℕ) → Σ (UU lzero) (λ m<n → is-prop m<n × is-decidable m<n)
decidable-subtype-le-ℕ n m =
  (le-ℕ m n , is-prop-le-ℕ m n , is-decidable-le-ℕ m n)
```

### If `m < n` then `n` must be nonzero

```agda
is-nonzero-le-ℕ : (m n : ℕ) → le-ℕ m n → is-nonzero-ℕ n
is-nonzero-le-ℕ m .zero-ℕ () refl
```

### Any nonzero natural number is strictly greater than `0`

```agda
le-is-nonzero-ℕ : (n : ℕ) → is-nonzero-ℕ n → le-ℕ zero-ℕ n
le-is-nonzero-ℕ zero-ℕ H = H refl
le-is-nonzero-ℕ (succ-ℕ n) H = star
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
```

### The strictly preordered set of natural numbers ordered by strict inequality

```agda
strictly-preordered-set-ℕ : Strictly-Preordered-Set lzero lzero
pr1 strictly-preordered-set-ℕ = ℕ-Set
pr2 strictly-preordered-set-ℕ =
  le-ℕ-Prop , anti-reflexive-le-ℕ , λ n m l I J → transitive-le-ℕ n m l J I
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

### `n < m` if and only if there exists a nonzero natural number `l` such that `l + n = m`

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
  tr (λ x → le-ℕ zero-ℕ x) p (le-is-nonzero-ℕ l q)
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

### If `n ≰ m` then `m < n`

```agda
le-not-leq-ℕ : (m n : ℕ) → ¬ (n ≤-ℕ m) → le-ℕ m n
le-not-leq-ℕ zero-ℕ zero-ℕ H = ex-falso (H star)
le-not-leq-ℕ zero-ℕ (succ-ℕ n) H = star
le-not-leq-ℕ (succ-ℕ m) zero-ℕ H = ex-falso (H star)
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

### If `x + 1 ≤ y` then `x < y`

```agda
le-leq-succ-ℕ :
  (x y : ℕ) → leq-ℕ (succ-ℕ x) y → le-ℕ x y
le-leq-succ-ℕ zero-ℕ (succ-ℕ y) H = star
le-leq-succ-ℕ (succ-ℕ x) (succ-ℕ y) H = le-leq-succ-ℕ x y H
```

### If `x ≤ y` then `x < y + 1`

```agda
le-succ-leq-ℕ :
  (x y : ℕ) → leq-ℕ x y → le-ℕ x (succ-ℕ y)
le-succ-leq-ℕ zero-ℕ y H = star
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

### For any two natural numbers `x` and `y`, either `x < y` or `y ≤ x`

```agda
decide-le-leq-ℕ : (x y : ℕ) → le-ℕ x y + leq-ℕ y x
decide-le-leq-ℕ x zero-ℕ = inr star
decide-le-leq-ℕ zero-ℕ (succ-ℕ _) = inl star
decide-le-leq-ℕ (succ-ℕ x) (succ-ℕ y) = decide-le-leq-ℕ x y
```

### If `1 < x` and `1 < y`, then `1 < xy`

```agda
le-one-mul-ℕ : (x y : ℕ) → 1 <-ℕ x → 1 <-ℕ y → 1 <-ℕ (x *ℕ y)
le-one-mul-ℕ (succ-ℕ (succ-ℕ x)) (succ-ℕ (succ-ℕ y)) star star = star
```

### Strict inequality on the natural numbers is invariant by translation

```agda
eq-translate-right-le-ℕ : (z x y : ℕ) → le-ℕ (x +ℕ z) (y +ℕ z) ＝ le-ℕ x y
eq-translate-right-le-ℕ zero-ℕ x y = refl
eq-translate-right-le-ℕ (succ-ℕ z) x y = eq-translate-right-le-ℕ z x y

eq-translate-left-le-ℕ : (z x y : ℕ) → le-ℕ (z +ℕ x) (z +ℕ y) ＝ le-ℕ x y
eq-translate-left-le-ℕ z x y =
  ap-binary le-ℕ (commutative-add-ℕ z x) (commutative-add-ℕ z y) ∙
  eq-translate-right-le-ℕ z x y
```

### Addition on the natural numbers preserves strict inequality

```agda
preserves-le-right-add-ℕ : (z x y : ℕ) → le-ℕ x y → le-ℕ (x +ℕ z) (y +ℕ z)
preserves-le-right-add-ℕ zero-ℕ x y I = I
preserves-le-right-add-ℕ (succ-ℕ z) x y I = preserves-le-right-add-ℕ z x y I

preserves-le-left-add-ℕ : (z x y : ℕ) → le-ℕ x y → le-ℕ (z +ℕ x) (z +ℕ y)
preserves-le-left-add-ℕ z x y I =
  binary-tr
    le-ℕ
    (commutative-add-ℕ x z)
    (commutative-add-ℕ y z)
    (preserves-le-right-add-ℕ z x y I)

preserves-le-add-ℕ :
  {a b c d : ℕ} → le-ℕ a b → le-ℕ c d → le-ℕ (a +ℕ c) (b +ℕ d)
preserves-le-add-ℕ {a} {b} {c} {d} H K =
  transitive-le-ℕ
    (a +ℕ c)
    (b +ℕ c)
    (b +ℕ d)
    (preserves-le-right-add-ℕ c a b H)
    (preserves-le-left-add-ℕ b c d K)
```

### There is an equivalence between natural numbers less than `succ-ℕ n` and natural numbers less than or equal to `n`

```agda
equiv-le-succ-ℕ-leq-ℕ :
  (n : ℕ) → Σ ℕ (λ k → le-ℕ k (succ-ℕ n)) ≃ Σ ℕ (λ k → leq-ℕ k n)
pr1 (equiv-le-succ-ℕ-leq-ℕ n) (k , k<sn) = (k , leq-le-succ-ℕ k n k<sn)
pr2 (equiv-le-succ-ℕ-leq-ℕ n) =
  is-equiv-is-invertible
    ( λ (k , k≤n) → k , le-succ-leq-ℕ k n k≤n)
    ( λ (k , k≤n) → eq-pair-eq-fiber (eq-type-Prop (leq-ℕ-Prop k n)))
    ( λ (k , k<sn) → eq-pair-eq-fiber (eq-type-Prop (le-ℕ-Prop k (succ-ℕ n))))
```
