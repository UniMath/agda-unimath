# The classical definition of the standard finite types

```agda
module univalent-combinatorics.classical-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Classically, the standard type with n elements is defined to be `{0,1,...,n-1}`,
i.e., it is the type of natural numbers strictly less than n.

## Definitions

### The classical definition of the finite types

```agda
classical-Fin : ℕ → UU lzero
classical-Fin k = Σ ℕ (λ x → le-ℕ x k)
```

### The inclusion from `classical-Fin` to ℕ

```agda
nat-classical-Fin : (k : ℕ) → classical-Fin k → ℕ
nat-classical-Fin k = pr1
```

## Properties

### Characterization of equality

```agda
Eq-classical-Fin : (k : ℕ) (x y : classical-Fin k) → UU lzero
Eq-classical-Fin k x y = Id (nat-classical-Fin k x) (nat-classical-Fin k y)

eq-succ-classical-Fin :
  (k : ℕ) (x y : classical-Fin k) → Id {A = classical-Fin k} x y →
  Id
    { A = classical-Fin (succ-ℕ k)}
    ( pair (succ-ℕ (pr1 x)) (pr2 x))
    ( pair (succ-ℕ (pr1 y)) (pr2 y))
eq-succ-classical-Fin k x .x refl = refl

eq-Eq-classical-Fin :
  (k : ℕ) (x y : classical-Fin k) → Eq-classical-Fin k x y → x ＝ y
eq-Eq-classical-Fin (succ-ℕ k) (pair zero-ℕ _) (pair zero-ℕ _) e = refl
eq-Eq-classical-Fin (succ-ℕ k) (pair (succ-ℕ x) p) (pair (succ-ℕ y) q) e =
  eq-succ-classical-Fin k
    ( pair x p)
    ( pair y q)
    ( eq-Eq-classical-Fin k (pair x p) (pair y q) (is-injective-succ-ℕ e))

Eq-eq-classical-Fin :
  (k : ℕ) (x y : classical-Fin k) → x ＝ y → Eq-classical-Fin k x y
Eq-eq-classical-Fin k x y refl = refl
```

### The classical finite types are equivalent to the standard finite types

#### We define maps back and forth between the standard finite sets and the bounded natural numbers

```agda
standard-classical-Fin : (k : ℕ) → classical-Fin k → Fin k
standard-classical-Fin (succ-ℕ k) (pair x H) = mod-succ-ℕ k x

classical-standard-Fin :
  (k : ℕ) → Fin k → classical-Fin k
pr1 (classical-standard-Fin k x) = nat-Fin k x
pr2 (classical-standard-Fin k x) = strict-upper-bound-nat-Fin k x
```

#### We show that these maps are mutual inverses

```agda
is-section-classical-standard-Fin :
  {k : ℕ} (x : Fin k) →
  Id (standard-classical-Fin k (classical-standard-Fin k x)) x
is-section-classical-standard-Fin {succ-ℕ k} x = is-section-nat-Fin k x

is-retraction-classical-standard-Fin :
  {k : ℕ} (x : classical-Fin k) →
  Id (classical-standard-Fin k (standard-classical-Fin k x)) x
is-retraction-classical-standard-Fin {succ-ℕ k} (pair x p) =
  eq-Eq-classical-Fin (succ-ℕ k)
    ( classical-standard-Fin
      ( succ-ℕ k)
      ( standard-classical-Fin (succ-ℕ k) (pair x p)))
    ( pair x p)
    ( eq-cong-le-ℕ
      ( succ-ℕ k)
      ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k x))
      ( x)
      ( strict-upper-bound-nat-Fin (succ-ℕ k) (mod-succ-ℕ k x))
      ( p)
      ( cong-nat-mod-succ-ℕ k x))
```

#### The standard equivalence

```agda
equiv-classical-standard-Fin : (n : ℕ) → Fin n ≃ classical-Fin n
pr1 (equiv-classical-standard-Fin n) = classical-standard-Fin n
pr2 (equiv-classical-standard-Fin n) =
  is-equiv-is-invertible
    ( standard-classical-Fin n)
    ( is-retraction-classical-standard-Fin {n})
    ( is-section-classical-standard-Fin {n})
```

### The reverse equivalence

The equivalence based on `nat-Fin-reverse` is occasionally useful.

#### We define the reversed maps back and forth between the standard finite sets and the bounded natural numbers

```agda
classical-standard-Fin-reverse : (n : ℕ) (k : Fin n) → classical-Fin n
classical-standard-Fin-reverse (succ-ℕ n) (inr star) = zero-ℕ , star
classical-standard-Fin-reverse (succ-ℕ n) (inl k) =
  ind-Σ (λ m m<n → (succ-ℕ m , m<n)) (classical-standard-Fin-reverse n k)

standard-classical-Fin-reverse : (n : ℕ) → Σ ℕ (λ k → le-ℕ k n) → Fin n
standard-classical-Fin-reverse (succ-ℕ n) (zero-ℕ , star) = inr star
standard-classical-Fin-reverse (succ-ℕ n) (succ-ℕ k , H) =
  inl (standard-classical-Fin-reverse n (k , H))
```

#### We show that these maps are mutual inverses

```agda
is-section-classical-standard-Fin-reverse :
  (n : ℕ) →
  is-section
    ( classical-standard-Fin-reverse n)
    ( standard-classical-Fin-reverse n)
is-section-classical-standard-Fin-reverse (succ-ℕ n) (zero-ℕ , k<n) = refl
is-section-classical-standard-Fin-reverse (succ-ℕ n) (succ-ℕ k , k<n) =
  eq-pair-Σ
    ( ap (succ-ℕ ∘ pr1) (is-section-classical-standard-Fin-reverse n (k , k<n)))
    ( eq-type-Prop (le-ℕ-Prop k n))

is-retraction-classical-standard-Fin-reverse :
  (n : ℕ) →
  is-retraction
    ( classical-standard-Fin-reverse n)
    ( standard-classical-Fin-reverse n)
is-retraction-classical-standard-Fin-reverse (succ-ℕ n) (inl x) =
  ap inl (is-retraction-classical-standard-Fin-reverse n x)
is-retraction-classical-standard-Fin-reverse (succ-ℕ n) (inr star) = refl
```

#### The reversed equivalence

```agda
equiv-classical-standard-Fin-reverse : (n : ℕ) → Fin n ≃ classical-Fin n
pr1 (equiv-classical-standard-Fin-reverse n) = classical-standard-Fin-reverse n
pr2 (equiv-classical-standard-Fin-reverse n) =
  is-equiv-is-invertible
    ( standard-classical-Fin-reverse n)
    ( is-section-classical-standard-Fin-reverse n)
    ( is-retraction-classical-standard-Fin-reverse n)
```

## See also

- [Standard finite types](univalent-combinatorics.classical-finite-types.md), an
  inductively constructed set of `n` distinct elements
