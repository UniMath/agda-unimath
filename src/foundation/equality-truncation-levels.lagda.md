# Equality of truncation levels

```agda
module foundation.equality-truncation-levels where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.decidable-propositions
open import foundation-core.discrete-types
open import foundation-core.empty-types
open import foundation-core.sets
open import foundation-core.torsorial-type-families
```

</details>

## Idea

The [type of truncation levels](foundation-core.truncation-levels.md) `𝕋` has
[decidable equality](foundation.decidable-equality.md).

## Definitions

### Observational equality on truncation levels

```agda
Eq-𝕋 : 𝕋 → 𝕋 → UU lzero
Eq-𝕋 neg-two-𝕋 neg-two-𝕋 = unit
Eq-𝕋 neg-two-𝕋 (succ-𝕋 r) = empty
Eq-𝕋 (succ-𝕋 k) neg-two-𝕋 = empty
Eq-𝕋 (succ-𝕋 k) (succ-𝕋 r) = Eq-𝕋 k r
```

## Properties

### The type of truncation levels is a set

```agda
abstract
  is-prop-Eq-𝕋 :
    (n m : 𝕋) → is-prop (Eq-𝕋 n m)
  is-prop-Eq-𝕋 neg-two-𝕋 neg-two-𝕋 = is-prop-unit
  is-prop-Eq-𝕋 neg-two-𝕋 (succ-𝕋 m) = is-prop-empty
  is-prop-Eq-𝕋 (succ-𝕋 n) neg-two-𝕋 = is-prop-empty
  is-prop-Eq-𝕋 (succ-𝕋 n) (succ-𝕋 m) = is-prop-Eq-𝕋 n m

refl-Eq-𝕋 : (n : 𝕋) → Eq-𝕋 n n
refl-Eq-𝕋 neg-two-𝕋 = star
refl-Eq-𝕋 (succ-𝕋 n) = refl-Eq-𝕋 n

Eq-eq-𝕋 : {x y : 𝕋} → x ＝ y → Eq-𝕋 x y
Eq-eq-𝕋 {x} {.x} refl = refl-Eq-𝕋 x

eq-Eq-𝕋 : (x y : 𝕋) → Eq-𝕋 x y → x ＝ y
eq-Eq-𝕋 neg-two-𝕋 neg-two-𝕋 e = refl
eq-Eq-𝕋 (succ-𝕋 x) (succ-𝕋 y) e = ap succ-𝕋 (eq-Eq-𝕋 x y e)

abstract
  is-set-𝕋 : is-set 𝕋
  is-set-𝕋 = is-set-prop-in-id Eq-𝕋 is-prop-Eq-𝕋 refl-Eq-𝕋 eq-Eq-𝕋

𝕋-Set : Set lzero
pr1 𝕋-Set = 𝕋
pr2 𝕋-Set = is-set-𝕋
```

### The property of being negative two

```agda
is-neg-two-𝕋 : 𝕋 → UU lzero
is-neg-two-𝕋 = _＝ neg-two-𝕋

is-prop-is-neg-two-𝕋 : (n : 𝕋) → is-prop (is-neg-two-𝕋 n)
is-prop-is-neg-two-𝕋 n = is-set-𝕋 n neg-two-𝕋

is-neg-two-𝕋-Prop : 𝕋 → Prop lzero
is-neg-two-𝕋-Prop n = (is-neg-two-𝕋 n , is-prop-is-neg-two-𝕋 n)
```

### The property of being negative one

```agda
is-neg-one-𝕋 : 𝕋 → UU lzero
is-neg-one-𝕋 = _＝ neg-one-𝕋

is-prop-is-neg-one-𝕋 : (n : 𝕋) → is-prop (is-neg-one-𝕋 n)
is-prop-is-neg-one-𝕋 n = is-set-𝕋 n neg-one-𝕋

is-neg-one-𝕋-Prop : 𝕋 → Prop lzero
is-neg-one-𝕋-Prop n = (is-neg-one-𝕋 n , is-prop-is-neg-one-𝕋 n)
```

### The type of truncation levels has decidable equality

```agda
is-decidable-Eq-𝕋 :
  (m n : 𝕋) → is-decidable (Eq-𝕋 m n)
is-decidable-Eq-𝕋 neg-two-𝕋 neg-two-𝕋 = inl star
is-decidable-Eq-𝕋 neg-two-𝕋 (succ-𝕋 n) = inr id
is-decidable-Eq-𝕋 (succ-𝕋 m) neg-two-𝕋 = inr id
is-decidable-Eq-𝕋 (succ-𝕋 m) (succ-𝕋 n) = is-decidable-Eq-𝕋 m n

has-decidable-equality-𝕋 : has-decidable-equality 𝕋
has-decidable-equality-𝕋 x y =
  is-decidable-iff (eq-Eq-𝕋 x y) Eq-eq-𝕋 (is-decidable-Eq-𝕋 x y)

𝕋-Discrete-Type : Discrete-Type lzero
𝕋-Discrete-Type = (𝕋 , has-decidable-equality-𝕋)

decidable-eq-𝕋 : 𝕋 → 𝕋 → Decidable-Prop lzero
pr1 (decidable-eq-𝕋 m n) = (m ＝ n)
pr1 (pr2 (decidable-eq-𝕋 m n)) = is-set-𝕋 m n
pr2 (pr2 (decidable-eq-𝕋 m n)) = has-decidable-equality-𝕋 m n

is-decidable-is-neg-two-𝕋 : (n : 𝕋) → is-decidable (is-neg-two-𝕋 n)
is-decidable-is-neg-two-𝕋 n = has-decidable-equality-𝕋 n neg-two-𝕋

is-decidable-is-neg-two-𝕋' : (n : 𝕋) → is-decidable (neg-two-𝕋 ＝ n)
is-decidable-is-neg-two-𝕋' n = has-decidable-equality-𝕋 neg-two-𝕋 n

is-decidable-is-neg-one-𝕋 : (n : 𝕋) → is-decidable (is-neg-one-𝕋 n)
is-decidable-is-neg-one-𝕋 n = has-decidable-equality-𝕋 n neg-one-𝕋

is-decidable-is-neg-one-𝕋' : (n : 𝕋) → is-decidable (neg-one-𝕋 ＝ n)
is-decidable-is-neg-one-𝕋' n = has-decidable-equality-𝕋 neg-one-𝕋 n
```

## The full characterization of identifications of truncation levels

```agda
map-total-Eq-𝕋 : (m : 𝕋) → Σ 𝕋 (Eq-𝕋 m) → Σ 𝕋 (Eq-𝕋 (succ-𝕋 m))
map-total-Eq-𝕋 m (n , e) = (succ-𝕋 n , e)

is-torsorial-Eq-𝕋 : (m : 𝕋) → is-torsorial (Eq-𝕋 m)
pr1 (pr1 (is-torsorial-Eq-𝕋 m)) = m
pr2 (pr1 (is-torsorial-Eq-𝕋 m)) = refl-Eq-𝕋 m
pr2 (is-torsorial-Eq-𝕋 neg-two-𝕋) (neg-two-𝕋 , *) = refl
pr2 (is-torsorial-Eq-𝕋 (succ-𝕋 m)) (succ-𝕋 n , e) =
  ap (map-total-Eq-𝕋 m) (pr2 (is-torsorial-Eq-𝕋 m) (n , e))

is-equiv-Eq-eq-𝕋 : {m n : 𝕋} → is-equiv (Eq-eq-𝕋 {m} {n})
is-equiv-Eq-eq-𝕋 {m} {n} =
  fundamental-theorem-id (is-torsorial-Eq-𝕋 m) (λ y → Eq-eq-𝕋 {m} {y}) n

extensionality-𝕋 : {m n : 𝕋} → (m ＝ n) ≃ Eq-𝕋 m n
extensionality-𝕋 = (Eq-eq-𝕋 , is-equiv-Eq-eq-𝕋)
```
