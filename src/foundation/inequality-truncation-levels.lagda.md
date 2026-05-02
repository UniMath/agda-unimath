# Inequality of truncation levels

```agda
module foundation.inequality-truncation-levels where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equality-truncation-levels
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.decidable-posets
open import order-theory.decidable-total-orders
open import order-theory.posets
open import order-theory.preorders
open import order-theory.total-orders
```

</details>

## Idea

The ordering `≤` on [truncation levels](foundation-core.truncation-levels.md)
mirrors the
[ordering on integers](elementary-number-theory.inequality-integers.md) greater
than or equal to `-2`.

## Definitions

### Inequality of truncation levels

```agda
leq-𝕋 : 𝕋 → 𝕋 → UU lzero
leq-𝕋 neg-two-𝕋 m = unit
leq-𝕋 (succ-𝕋 n) neg-two-𝕋 = empty
leq-𝕋 (succ-𝕋 n) (succ-𝕋 m) = leq-𝕋 n m

infix 30 _≤-𝕋_
_≤-𝕋_ : 𝕋 → 𝕋 → UU lzero
_≤-𝕋_ = leq-𝕋
```

### Alternative definition of the inequality of truncation levels

```agda
data leq-𝕋' : 𝕋 → 𝕋 → UU lzero where
  refl-leq-𝕋' : (n : 𝕋) → leq-𝕋' n n
  propagate-leq-𝕋' : {x y z : 𝕋} → succ-𝕋 y ＝ z → (leq-𝕋' x y) → (leq-𝕋' x z)
```

## Properties

### Inequality of truncation levels is a proposition

```agda
is-prop-leq-𝕋 : (m n : 𝕋) → is-prop (leq-𝕋 m n)
is-prop-leq-𝕋 neg-two-𝕋 _ = is-prop-unit
is-prop-leq-𝕋 (succ-𝕋 m) neg-two-𝕋 = is-prop-empty
is-prop-leq-𝕋 (succ-𝕋 m) (succ-𝕋 n) = is-prop-leq-𝕋 m n

leq-𝕋-Prop : 𝕋 → 𝕋 → Prop lzero
leq-𝕋-Prop m n = (leq-𝕋 m n , is-prop-leq-𝕋 m n)
```

### Inequality of truncation levels is decidable

```agda
is-decidable-leq-𝕋 : (m n : 𝕋) → is-decidable (leq-𝕋 m n)
is-decidable-leq-𝕋 neg-two-𝕋 neg-two-𝕋 = inl star
is-decidable-leq-𝕋 neg-two-𝕋 (succ-𝕋 n) = inl star
is-decidable-leq-𝕋 (succ-𝕋 m) neg-two-𝕋 = inr id
is-decidable-leq-𝕋 (succ-𝕋 m) (succ-𝕋 n) = is-decidable-leq-𝕋 m n
```

### Inequality of truncation levels is a congruence

```agda
concatenate-eq-leq-eq-𝕋 :
  {x' x y y' : 𝕋} → x' ＝ x → x ≤-𝕋 y → y ＝ y' → x' ≤-𝕋 y'
concatenate-eq-leq-eq-𝕋 refl H refl = H

concatenate-leq-eq-𝕋 : (m : 𝕋) {n n' : 𝕋} → m ≤-𝕋 n → n ＝ n' → m ≤-𝕋 n'
concatenate-leq-eq-𝕋 m H refl = H

concatenate-eq-leq-𝕋 : {m m' : 𝕋} (n : 𝕋) → m' ＝ m → m ≤-𝕋 n → m' ≤-𝕋 n
concatenate-eq-leq-𝕋 n refl H = H
```

### Inequality of truncation levels is reflexive

```agda
refl-leq-𝕋 : (n : 𝕋) → n ≤-𝕋 n
refl-leq-𝕋 neg-two-𝕋 = star
refl-leq-𝕋 (succ-𝕋 n) = refl-leq-𝕋 n

leq-eq-𝕋 : (m n : 𝕋) → m ＝ n → m ≤-𝕋 n
leq-eq-𝕋 m .m refl = refl-leq-𝕋 m
```

### Inequality of truncation levels is transitive

```agda
transitive-leq-𝕋 : is-transitive leq-𝕋
transitive-leq-𝕋 neg-two-𝕋 m l p q = star
transitive-leq-𝕋 (succ-𝕋 n) (succ-𝕋 m) (succ-𝕋 l) p q =
  transitive-leq-𝕋 n m l p q
```

### Inequality of truncation levels is antisymmetric

```agda
antisymmetric-leq-𝕋 : (m n : 𝕋) → m ≤-𝕋 n → n ≤-𝕋 m → m ＝ n
antisymmetric-leq-𝕋 neg-two-𝕋 neg-two-𝕋 p q = refl
antisymmetric-leq-𝕋 (succ-𝕋 m) (succ-𝕋 n) p q =
  ap succ-𝕋 (antisymmetric-leq-𝕋 m n p q)
```

### For any two truncation levels we can decide which one is less than the other

```agda
linear-leq-𝕋 : (m n : 𝕋) → (m ≤-𝕋 n) + (n ≤-𝕋 m)
linear-leq-𝕋 neg-two-𝕋 neg-two-𝕋 = inl star
linear-leq-𝕋 neg-two-𝕋 (succ-𝕋 n) = inl star
linear-leq-𝕋 (succ-𝕋 m) neg-two-𝕋 = inr star
linear-leq-𝕋 (succ-𝕋 m) (succ-𝕋 n) = linear-leq-𝕋 m n

abstract
  is-total-leq-𝕋 : (m n : 𝕋) → disjunction-type (m ≤-𝕋 n) (n ≤-𝕋 m)
  is-total-leq-𝕋 m n = unit-trunc-Prop (linear-leq-𝕋 m n)
```

### For any three truncation levels, there are three cases in how they can be ordered

```agda
cases-order-three-elements-𝕋 : (x y z : 𝕋) → UU lzero
cases-order-three-elements-𝕋 x y z =
  ( ( leq-𝕋 x y × leq-𝕋 y z) +
    ( leq-𝕋 x z × leq-𝕋 z y)) +
  ( ( ( leq-𝕋 y z × leq-𝕋 z x) +
      ( leq-𝕋 y x × leq-𝕋 x z)) +
    ( ( leq-𝕋 z x × leq-𝕋 x y) +
      (leq-𝕋 z y × leq-𝕋 y x)))

order-three-elements-𝕋 : (x y z : 𝕋) → cases-order-three-elements-𝕋 x y z
order-three-elements-𝕋 neg-two-𝕋 neg-two-𝕋 neg-two-𝕋 = inl (inl (star , star))
order-three-elements-𝕋 neg-two-𝕋 neg-two-𝕋 (succ-𝕋 z) = inl (inl (star , star))
order-three-elements-𝕋 neg-two-𝕋 (succ-𝕋 y) neg-two-𝕋 = inl (inr (star , star))
order-three-elements-𝕋 neg-two-𝕋 (succ-𝕋 y) (succ-𝕋 z) =
  inl (map-coproduct (pair star) (pair star) (linear-leq-𝕋 y z))
order-three-elements-𝕋 (succ-𝕋 x) neg-two-𝕋 neg-two-𝕋 =
  inr (inl (inl (star , star)))
order-three-elements-𝕋 (succ-𝕋 x) neg-two-𝕋 (succ-𝕋 z) =
  inr (inl (map-coproduct (pair star) (pair star) (linear-leq-𝕋 z x)))
order-three-elements-𝕋 (succ-𝕋 x) (succ-𝕋 y) neg-two-𝕋 =
  inr (inr (map-coproduct (pair star) (pair star) (linear-leq-𝕋 x y)))
order-three-elements-𝕋 (succ-𝕋 x) (succ-𝕋 y) (succ-𝕋 z) =
  order-three-elements-𝕋 x y z
```

### Zero is less than or equal to any truncation level

```agda
leq-neg-two-𝕋 : (n : 𝕋) → neg-two-𝕋 ≤-𝕋 n
leq-neg-two-𝕋 n = star
```

### Any truncation level less than -2 is -2

```agda
is-neg-two-leq-neg-two-𝕋 : (x : 𝕋) → x ≤-𝕋 neg-two-𝕋 → is-neg-two-𝕋 x
is-neg-two-leq-neg-two-𝕋 neg-two-𝕋 star = refl

is-neg-two-leq-neg-two-𝕋' : (x : 𝕋) → x ≤-𝕋 neg-two-𝕋 → neg-two-𝕋 ＝ x
is-neg-two-leq-neg-two-𝕋' neg-two-𝕋 star = refl
```

### Any truncation level is less than or equal to its own successor

```agda
succ-leq-𝕋 : (n : 𝕋) → n ≤-𝕋 (succ-𝕋 n)
succ-leq-𝕋 neg-two-𝕋 = star
succ-leq-𝕋 (succ-𝕋 n) = succ-leq-𝕋 n
```

### Any truncation level less than or equal to `n+1` is either less than or equal to `n` or it is `n+1`

```agda
decide-leq-succ-𝕋 :
  (m n : 𝕋) → m ≤-𝕋 (succ-𝕋 n) → (m ≤-𝕋 n) + (m ＝ succ-𝕋 n)
decide-leq-succ-𝕋 neg-two-𝕋 neg-two-𝕋 l = inl star
decide-leq-succ-𝕋 neg-two-𝕋 (succ-𝕋 n) l = inl star
decide-leq-succ-𝕋 (succ-𝕋 m) neg-two-𝕋 l =
  inr (ap succ-𝕋 (is-neg-two-leq-neg-two-𝕋 m l))
decide-leq-succ-𝕋 (succ-𝕋 m) (succ-𝕋 n) l =
  map-coproduct id (ap succ-𝕋) (decide-leq-succ-𝕋 m n l)
```

### If `m` is less than `n`, then it is less than `n+1`

```agda
preserves-order-succ-𝕋 : (m n : 𝕋) → m ≤-𝕋 n → m ≤-𝕋 (succ-𝕋 n)
preserves-order-succ-𝕋 m n = transitive-leq-𝕋 m n (succ-𝕋 n) (succ-leq-𝕋 n)
```

### The successor of `n` is not less than or equal to `n`

```agda
neg-succ-leq-𝕋 : (n : 𝕋) → ¬ (leq-𝕋 (succ-𝕋 n) n)
neg-succ-leq-𝕋 neg-two-𝕋 = id
neg-succ-leq-𝕋 (succ-𝕋 n) = neg-succ-leq-𝕋 n
```

### If `m ≤ n + 1` then either `m ≤ n` or `m = n + 1`

```agda
cases-leq-succ-𝕋 :
  {m n : 𝕋} → leq-𝕋 m (succ-𝕋 n) → (leq-𝕋 m n) + (m ＝ succ-𝕋 n)
cases-leq-succ-𝕋 {neg-two-𝕋} {n} star = inl star
cases-leq-succ-𝕋 {succ-𝕋 m} {neg-two-𝕋} p =
  inr (ap succ-𝕋 (antisymmetric-leq-𝕋 m neg-two-𝕋 p star))
cases-leq-succ-𝕋 {succ-𝕋 m} {succ-𝕋 n} p =
  map-coproduct id (ap succ-𝕋) (cases-leq-succ-𝕋 p)

cases-leq-succ-reflexive-leq-𝕋 :
  {n : 𝕋} → cases-leq-succ-𝕋 {succ-𝕋 n} {n} (refl-leq-𝕋 n) ＝ inr refl
cases-leq-succ-reflexive-leq-𝕋 {neg-two-𝕋} = refl
cases-leq-succ-reflexive-leq-𝕋 {succ-𝕋 n} =
  ap (map-coproduct id (ap succ-𝕋)) cases-leq-succ-reflexive-leq-𝕋
```

### `m ≤ n` if and only if `n + 1 ≰ m`

```agda
contradiction-leq-𝕋 : (m n : 𝕋) → m ≤-𝕋 n → ¬ (succ-𝕋 n ≤-𝕋 m)
contradiction-leq-𝕋 (succ-𝕋 m) (succ-𝕋 n) = contradiction-leq-𝕋 m n

contradiction-leq-𝕋' : (m n : 𝕋) → (succ-𝕋 n) ≤-𝕋 m → ¬ (m ≤-𝕋 n)
contradiction-leq-𝕋' m n K H = contradiction-leq-𝕋 m n H K
```

### The partially ordered set of truncation levels ordered by inequality

```agda
𝕋-Preorder : Preorder lzero lzero
𝕋-Preorder = (𝕋 , leq-𝕋-Prop , refl-leq-𝕋 , transitive-leq-𝕋)

𝕋-Poset : Poset lzero lzero
𝕋-Poset = (𝕋-Preorder , antisymmetric-leq-𝕋)

𝕋-Total-Order : Total-Order lzero lzero
𝕋-Total-Order = (𝕋-Poset , is-total-leq-𝕋)

𝕋-Decidable-Poset : Decidable-Poset lzero lzero
𝕋-Decidable-Poset = (𝕋-Poset , is-decidable-leq-𝕋)

𝕋-Decidable-Total-Order : Decidable-Total-Order lzero lzero
𝕋-Decidable-Total-Order = (𝕋-Poset , is-total-leq-𝕋 , is-decidable-leq-𝕋)
```
