# Strict inequality on the standard finite types

```agda
module elementary-number-theory.strict-inequality-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-products-propositions
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Strict inequality on the
[standard finite types](univalent-combinatorics.standard-finite-types.md) is
defined inductively with the rule that `inl-Fin k < neg-one-Fin n`, and
`inl-Fin a < inl-Fin b` if `a < b`.

## Definitions

### The strict inequality relation on the standard finite types

```agda
le-prop-Fin : (k : ℕ) → Fin k → Fin k → Prop lzero
le-prop-Fin (succ-ℕ k) (inl x) (inl y) = le-prop-Fin k x y
le-prop-Fin (succ-ℕ k) (inl x) (inr star) = unit-Prop
le-prop-Fin (succ-ℕ k) (inr star) y = empty-Prop

le-Fin : (k : ℕ) → Fin k → Fin k → UU lzero
le-Fin k x y = type-Prop (le-prop-Fin k x y)

abstract
  is-prop-le-Fin :
    (k : ℕ) (x y : Fin k) → is-prop (le-Fin k x y)
  is-prop-le-Fin k x y = is-prop-type-Prop (le-prop-Fin k x y)
```

### The predicate on maps between standard finite types of preserving strict inequality

```agda
preserves-strict-order-Fin : (n m : ℕ) → (Fin n → Fin m) → UU lzero
preserves-strict-order-Fin n m f =
  (a b : Fin n) →
  le-Fin n a b →
  le-Fin m (f a) (f b)

abstract
  is-prop-preserves-strict-order-Fin :
    (n m : ℕ) (f : Fin n → Fin m) →
    is-prop (preserves-strict-order-Fin n m f)
  is-prop-preserves-strict-order-Fin n m f =
    is-prop-Π λ a →
    is-prop-Π λ b →
    is-prop-Π λ p →
    is-prop-le-Fin m (f a) (f b)
```

### A map `Fin (succ-ℕ m) → Fin (succ-ℕ n)` preserving strict inequality restricts to a map `Fin m → Fin n`

#### The induced map obtained by restricting

```agda
restriction-preserves-strict-order-Fin' :
  (m n : ℕ) (f : Fin (succ-ℕ m) → Fin (succ-ℕ n)) →
  (preserves-strict-order-Fin (succ-ℕ m) (succ-ℕ n) f) →
  (x : Fin m) → (y : Fin (succ-ℕ n)) →
  (f (inl x) ＝ y) → Fin n
restriction-preserves-strict-order-Fin' (succ-ℕ m) n f pf x (inl y) p = y
restriction-preserves-strict-order-Fin' (succ-ℕ m) n f pf x (inr y) p =
  ex-falso
    ( tr (λ - → le-Fin (succ-ℕ n) - (f (inr star))) p
      ( pf (inl x) (inr star) star))

restriction-preserves-strict-order-Fin :
  (m n : ℕ) (f : Fin (succ-ℕ m) → Fin (succ-ℕ n)) →
  (preserves-strict-order-Fin (succ-ℕ m) (succ-ℕ n) f) →
  Fin m → Fin n
restriction-preserves-strict-order-Fin m n f pf x =
  restriction-preserves-strict-order-Fin' m n f pf x (f (inl x)) refl
```

#### The induced map is indeed a restriction

```agda
abstract
  inl-restriction-preserves-strict-order-Fin' :
    (m n : ℕ) (f : Fin (succ-ℕ m) → Fin (succ-ℕ n)) →
    (pf : preserves-strict-order-Fin (succ-ℕ m) (succ-ℕ n) f) →
    (x : Fin m) →
    (rx : Fin (succ-ℕ n)) →
    (px : f (inl x) ＝ rx) →
    inl-Fin n (restriction-preserves-strict-order-Fin' m n f pf x rx px) ＝
    f (inl-Fin m x)
  inl-restriction-preserves-strict-order-Fin' (succ-ℕ m) n f pf x (inl a) px = inv px
  inl-restriction-preserves-strict-order-Fin' (succ-ℕ m) n f pf x (inr a) px =
    ex-falso
      ( tr (λ - → le-Fin (succ-ℕ n) - (f (inr star))) px
        ( pf (inl x) (inr star) star))

  inl-restriction-preserves-strict-order-Fin :
    (m n : ℕ) (f : Fin (succ-ℕ m) → Fin (succ-ℕ n)) →
    (pf : preserves-strict-order-Fin (succ-ℕ m) (succ-ℕ n) f) →
    (x : Fin m) →
    inl-Fin n (restriction-preserves-strict-order-Fin m n f pf x) ＝ f (inl-Fin m x)
  inl-restriction-preserves-strict-order-Fin m n f pf x =
    inl-restriction-preserves-strict-order-Fin' m n f pf x (f (inl x)) refl
```

#### The induced map preserves strict inequality

```agda
abstract
  preserves-strict-order-restriction-preserves-strict-order-Fin' :
    (m n : ℕ) (f : Fin (succ-ℕ m) → Fin (succ-ℕ n)) →
    (pf : preserves-strict-order-Fin (succ-ℕ m) (succ-ℕ n) f) →
    ( a : Fin m)
    ( b : Fin m) →
    ( ra : Fin (succ-ℕ n)) →
    ( pa : f (inl a) ＝ ra) →
    ( rb : Fin (succ-ℕ n)) →
    ( pb : f (inl b) ＝ rb) →
    le-Fin m a b →
    le-Fin n
      (restriction-preserves-strict-order-Fin' m n f pf a ra pa)
      (restriction-preserves-strict-order-Fin' m n f pf b rb pb)
  preserves-strict-order-restriction-preserves-strict-order-Fin'
    (succ-ℕ m) n f pf a b (inl x) pa (inl y) pb H =
    tr (le-Fin (succ-ℕ n) (inl x)) pb
      ( tr (λ - → le-Fin (succ-ℕ n) - (f (inl b))) pa
      ( pf (inl a) (inl b) H))
  preserves-strict-order-restriction-preserves-strict-order-Fin'
    (succ-ℕ m) n f pf a b (inl x) pa (inr y) pb H =
    ex-falso
      ( tr (λ - → le-Fin (succ-ℕ n) - (f (inr star))) pb
        ( pf (inl b) (inr star) star))
  preserves-strict-order-restriction-preserves-strict-order-Fin'
    (succ-ℕ m) n f pf a b (inr x) pa y pb H =
    ex-falso
      ( tr (λ - → le-Fin (succ-ℕ n) - (f (inr star))) pa
        ( pf (inl a) (inr star) star))

  preserves-strict-order-restriction-preserves-strict-order-Fin :
    (m n : ℕ) (f : Fin (succ-ℕ m) → Fin (succ-ℕ n)) →
    (pf : preserves-strict-order-Fin (succ-ℕ m) (succ-ℕ n) f) →
    preserves-strict-order-Fin m n (restriction-preserves-strict-order-Fin m n f pf)
  preserves-strict-order-restriction-preserves-strict-order-Fin m n f pf a b H =
    preserves-strict-order-restriction-preserves-strict-order-Fin' m n f pf a b
      ( f (inl a)) refl (f (inl b)) refl H
```

### A strict inequality preserving map implies an inequality of cardinalities

```agda
abstract
  leq-preserves-strict-order-Fin :
    (m n : ℕ) → (f : Fin m → Fin n) →
    preserves-strict-order-Fin m n f → leq-ℕ m n
  leq-preserves-strict-order-Fin 0 0 f pf = star
  leq-preserves-strict-order-Fin 0 (succ-ℕ n) f pf = star
  leq-preserves-strict-order-Fin (succ-ℕ m) 0 f pf = f (inr star)
  leq-preserves-strict-order-Fin (succ-ℕ 0) (succ-ℕ n) f pf = star
  leq-preserves-strict-order-Fin (succ-ℕ (succ-ℕ m)) (succ-ℕ n) f pf =
    leq-preserves-strict-order-Fin (succ-ℕ m) n
      ( restriction-preserves-strict-order-Fin (succ-ℕ m) n f pf)
      ( preserves-strict-order-restriction-preserves-strict-order-Fin (succ-ℕ m) n f pf)
```

### Composition of strict inequality preserving maps

```agda
abstract
  comp-preserves-strict-order-Fin :
    (m n o : ℕ)
    (g : Fin n → Fin o)
    (f : Fin m → Fin n) →
    preserves-strict-order-Fin m n f →
    preserves-strict-order-Fin n o g →
    preserves-strict-order-Fin m o (g ∘ f)
  comp-preserves-strict-order-Fin m n o g f pf pg a b H =
    pg (f a) (f b) (pf a b H)
```
