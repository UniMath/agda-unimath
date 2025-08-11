# The maximum of truncation levels

```agda
module foundation.maximum-truncation-levels where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.inequality-truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.truncated-types
open import foundation-core.truncation-levels

open import order-theory.least-upper-bounds-posets
```

</details>

## Idea

Given two [truncation levels](foundation-core.truncation-levels.md) $k$ and $r$,
the
{{#concept "maximum" Disambiguation="binary maximum of truncation levels" Agda=max-𝕋}}
of $k$ and $r$ is the largest of the two.

## Definitions

### The maximum of two truncation levels

```agda
max-𝕋 : 𝕋 → 𝕋 → 𝕋
max-𝕋 neg-two-𝕋 r = r
max-𝕋 (succ-𝕋 k) neg-two-𝕋 = succ-𝕋 k
max-𝕋 (succ-𝕋 k) (succ-𝕋 r) = succ-𝕋 (max-𝕋 k r)

infixl 35 _⊔𝕋_
_⊔𝕋_ : 𝕋 → 𝕋 → 𝕋
_⊔𝕋_ = max-𝕋

max-𝕋' : 𝕋 → 𝕋 → 𝕋
max-𝕋' k r = max-𝕋 r k
```

## Properties

### The unit laws for the maximum operation

```agda
left-unit-law-𝕋 : {k : 𝕋} → neg-two-𝕋 ⊔𝕋 k ＝ k
left-unit-law-𝕋 = refl

right-unit-law-𝕋 : {k : 𝕋} → k ⊔𝕋 neg-two-𝕋 ＝ k
right-unit-law-𝕋 {neg-two-𝕋} = refl
right-unit-law-𝕋 {succ-𝕋 k} = refl

inv-right-unit-law-𝕋 : {k : 𝕋} → k ＝ k ⊔𝕋 neg-two-𝕋
inv-right-unit-law-𝕋 {neg-two-𝕋} = refl
inv-right-unit-law-𝕋 {succ-𝕋 k} = refl
```

### The maximum is a least upper bound

```agda
leq-max-𝕋 : (k m n : 𝕋) → m ≤-𝕋 k → n ≤-𝕋 k → m ⊔𝕋 n ≤-𝕋 k
leq-max-𝕋 neg-two-𝕋 neg-two-𝕋 neg-two-𝕋 H K = star
leq-max-𝕋 (succ-𝕋 k) neg-two-𝕋 neg-two-𝕋 H K = star
leq-max-𝕋 (succ-𝕋 k) neg-two-𝕋 (succ-𝕋 n) H K = K
leq-max-𝕋 (succ-𝕋 k) (succ-𝕋 m) neg-two-𝕋 H K = H
leq-max-𝕋 (succ-𝕋 k) (succ-𝕋 m) (succ-𝕋 n) H K = leq-max-𝕋 k m n H K

leq-left-leq-max-𝕋 : (k m n : 𝕋) → m ⊔𝕋 n ≤-𝕋 k → m ≤-𝕋 k
leq-left-leq-max-𝕋 k neg-two-𝕋 neg-two-𝕋 H = star
leq-left-leq-max-𝕋 k neg-two-𝕋 (succ-𝕋 n) H = star
leq-left-leq-max-𝕋 k (succ-𝕋 m) neg-two-𝕋 H = H
leq-left-leq-max-𝕋 (succ-𝕋 k) (succ-𝕋 m) (succ-𝕋 n) H =
  leq-left-leq-max-𝕋 k m n H

leq-right-leq-max-𝕋 : (k m n : 𝕋) → m ⊔𝕋 n ≤-𝕋 k → n ≤-𝕋 k
leq-right-leq-max-𝕋 k neg-two-𝕋 neg-two-𝕋 H = star
leq-right-leq-max-𝕋 k neg-two-𝕋 (succ-𝕋 n) H = H
leq-right-leq-max-𝕋 k (succ-𝕋 m) neg-two-𝕋 H = star
leq-right-leq-max-𝕋 (succ-𝕋 k) (succ-𝕋 m) (succ-𝕋 n) H =
  leq-right-leq-max-𝕋 k m n H

left-leq-max-𝕋 : (m n : 𝕋) → m ≤-𝕋 m ⊔𝕋 n
left-leq-max-𝕋 m n = leq-left-leq-max-𝕋 (m ⊔𝕋 n) m n (refl-leq-𝕋 (m ⊔𝕋 n))

right-leq-max-𝕋 : (m n : 𝕋) → n ≤-𝕋 m ⊔𝕋 n
right-leq-max-𝕋 m n = leq-right-leq-max-𝕋 (m ⊔𝕋 n) m n (refl-leq-𝕋 (m ⊔𝕋 n))

is-least-upper-bound-max-𝕋 :
  (m n : 𝕋) → is-least-binary-upper-bound-Poset 𝕋-Poset m n (m ⊔𝕋 n)
is-least-upper-bound-max-𝕋 m n =
  prove-is-least-binary-upper-bound-Poset
    ( 𝕋-Poset)
    { m}
    { n}
    { m ⊔𝕋 n}
    ( left-leq-max-𝕋 m n , right-leq-max-𝕋 m n)
    ( λ x (H , K) → leq-max-𝕋 x m n H K)
```

### The maximum operation is associative

```agda
associative-max-𝕋 : (x y z : 𝕋) → (x ⊔𝕋 y) ⊔𝕋 z ＝ x ⊔𝕋 (y ⊔𝕋 z)
associative-max-𝕋 neg-two-𝕋 y z = refl
associative-max-𝕋 (succ-𝕋 x) neg-two-𝕋 neg-two-𝕋 = refl
associative-max-𝕋 (succ-𝕋 x) neg-two-𝕋 (succ-𝕋 z) = refl
associative-max-𝕋 (succ-𝕋 x) (succ-𝕋 y) neg-two-𝕋 = refl
associative-max-𝕋 (succ-𝕋 x) (succ-𝕋 y) (succ-𝕋 z) =
  ap succ-𝕋 (associative-max-𝕋 x y z)
```

### The maximum operation is commutative

```agda
commutative-max-𝕋 : {k r : 𝕋} → k ⊔𝕋 r ＝ r ⊔𝕋 k
commutative-max-𝕋 {neg-two-𝕋} {r} = inv-right-unit-law-𝕋
commutative-max-𝕋 {succ-𝕋 k} {neg-two-𝕋} = refl
commutative-max-𝕋 {succ-𝕋 k} {succ-𝕋 r} = ap succ-𝕋 (commutative-max-𝕋 {k} {r})
```

### The maximum operation is idempotent

```agda
idempotent-max-𝕋 : (x : 𝕋) → x ⊔𝕋 x ＝ x
idempotent-max-𝕋 neg-two-𝕋 = refl
idempotent-max-𝕋 (succ-𝕋 x) = ap succ-𝕋 (idempotent-max-𝕋 x)
```

### Successor diagonal laws for the maximum operation

```agda
left-successor-diagonal-law-max-𝕋 : (x : 𝕋) → succ-𝕋 x ⊔𝕋 x ＝ succ-𝕋 x
left-successor-diagonal-law-max-𝕋 neg-two-𝕋 = refl
left-successor-diagonal-law-max-𝕋 (succ-𝕋 x) =
  ap succ-𝕋 (left-successor-diagonal-law-max-𝕋 x)

right-successor-diagonal-law-max-𝕋 : (x : 𝕋) → x ⊔𝕋 succ-𝕋 x ＝ succ-𝕋 x
right-successor-diagonal-law-max-𝕋 neg-two-𝕋 = refl
right-successor-diagonal-law-max-𝕋 (succ-𝕋 x) =
  ap succ-𝕋 (right-successor-diagonal-law-max-𝕋 x)
```

### If a type is `k`-truncated and then it is `k ⊔ r`-truncated for every `r`

```agda
is-trunc-left-max-𝕋 :
  (k r : 𝕋) → {l : Level} {A : UU l} → is-trunc k A → is-trunc (k ⊔𝕋 r) A
is-trunc-left-max-𝕋 k neg-two-𝕋 =
  is-trunc-eq inv-right-unit-law-𝕋
is-trunc-left-max-𝕋 neg-two-𝕋 (succ-𝕋 r) H =
  is-trunc-is-contr (succ-𝕋 r) H
is-trunc-left-max-𝕋 (succ-𝕋 k) (succ-𝕋 r) H x y =
  is-trunc-left-max-𝕋 k r (H x y)

is-trunc-right-max-𝕋 :
  (k r : 𝕋) → {l : Level} {A : UU l} → is-trunc k A → is-trunc (r ⊔𝕋 k) A
is-trunc-right-max-𝕋 k neg-two-𝕋 = id
is-trunc-right-max-𝕋 neg-two-𝕋 (succ-𝕋 r) H =
  is-trunc-is-contr (succ-𝕋 r) H
is-trunc-right-max-𝕋 (succ-𝕋 k) (succ-𝕋 r) H x y =
  is-trunc-right-max-𝕋 k r (H x y)
```
