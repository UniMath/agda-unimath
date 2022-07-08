# Finite semigroups

```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-group-theory.finite-semigroups where

open import elementary-number-theory.natural-numbers using (ℕ; succ-ℕ; zero-ℕ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_; _∘e_; id-equiv)
open import foundation.functions using (_∘_)
open import foundation.functoriality-dependent-pair-types using (equiv-Σ)
open import foundation.mere-equivalences using (mere-equiv)
open import foundation.propositions using (is-proof-irrelevant-is-prop)
open import foundation.set-truncations using (type-trunc-Set)
open import foundation.sets using (is-prop-is-set; UU-Set; type-Set)
open import foundation.type-arithmetic-dependent-pair-types using
  ( right-unit-law-Σ-is-contr; equiv-right-swap-Σ)
open import foundation.universe-levels using (Level; UU; lsuc; lzero)

open import group-theory.semigroups using
  ( has-associative-mul; Semigroup; type-Semigroup; has-associative-mul-Set)

open import univalent-combinatorics.dependent-function-types using
  ( is-finite-Π)
open import univalent-combinatorics.dependent-sum-finite-types using
  ( is-finite-Σ)
open import univalent-combinatorics.equality-finite-types using
  ( is-finite-eq; has-decidable-equality-is-finite; is-set-is-finite)
open import univalent-combinatorics.finite-types using
  ( UU-Fin-Level; type-UU-Fin-Level; is-finite; is-finite-type-UU-Fin-Level;
    is-finite-has-cardinality)
open import univalent-combinatorics.function-types using
  ( is-finite-function-type)
open import univalent-combinatorics.pi-finite-types using
  ( is-π-finite; is-π-finite-Σ; is-π-finite-UU-Fin-Level; is-π-finite-is-finite;
    is-π-finite-equiv; number-of-connected-components;
    mere-equiv-number-of-connected-components)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

Finite semigroups are semigroups of which the underlying type is finite.

## Definition

### Semigroups of order n

```agda
Semigroup-of-Order' : (l : Level) (n : ℕ) → UU (lsuc l)
Semigroup-of-Order' l n =
  Σ ( UU-Fin-Level l n)
    ( λ X → has-associative-mul (type-UU-Fin-Level n X))

Semigroup-of-Order : (l : Level) (n : ℕ) → UU (lsuc l)
Semigroup-of-Order l n =
  Σ (Semigroup l) (λ G → mere-equiv (Fin n) (type-Semigroup G))
```

## Properties

### If `X` is finite, then there are finitely many associative operations on `X`

```agda
is-finite-has-associative-mul :
  {l : Level} {X : UU l} → is-finite X → is-finite (has-associative-mul X)
is-finite-has-associative-mul H =
  is-finite-Σ
    ( is-finite-function-type H (is-finite-function-type H H))
    ( λ μ →
      is-finite-Π H
        ( λ x →
          is-finite-Π H
            ( λ y →
              is-finite-Π H
                ( λ z →
                  is-finite-eq (has-decidable-equality-is-finite H)))))
```

### The type of semigroups of order n is π-finite

```agda
is-π-finite-Semigroup-of-Order' :
  {l : Level} (k n : ℕ) → is-π-finite k (Semigroup-of-Order' l n)
is-π-finite-Semigroup-of-Order' k n =
  is-π-finite-Σ k
    ( is-π-finite-UU-Fin-Level (succ-ℕ k) n)
    ( λ x →
      is-π-finite-is-finite k
        ( is-finite-has-associative-mul
          ( is-finite-type-UU-Fin-Level n x)))

is-π-finite-Semigroup-of-Order :
  {l : Level} (k n : ℕ) → is-π-finite k (Semigroup-of-Order l n)
is-π-finite-Semigroup-of-Order {l} k n =
  is-π-finite-equiv k e
    ( is-π-finite-Semigroup-of-Order' k n)
  where
  e : Semigroup-of-Order l n ≃ Semigroup-of-Order' l n
  e = ( equiv-Σ
        ( has-associative-mul ∘ type-UU-Fin-Level n)
        ( ( right-unit-law-Σ-is-contr
            ( λ X →
              is-proof-irrelevant-is-prop
                ( is-prop-is-set _)
                ( is-set-is-finite
                  ( is-finite-has-cardinality n (pr2 X))))) ∘e
          ( equiv-right-swap-Σ))
        ( λ X → id-equiv)) ∘e
      ( equiv-right-swap-Σ
        { A = UU-Set l}
        { B = has-associative-mul-Set}
        { C = mere-equiv (Fin n) ∘ type-Set})
```

### The function that returns for each `n` the number of semigroups of order `n` up to isomorphism

```agda
number-of-semi-groups-of-order : ℕ → ℕ
number-of-semi-groups-of-order n =
  number-of-connected-components
    ( is-π-finite-Semigroup-of-Order {lzero} zero-ℕ n)

mere-equiv-number-of-semi-groups-of-order :
  (n : ℕ) →
  mere-equiv
    ( Fin (number-of-semi-groups-of-order n))
    ( type-trunc-Set (Semigroup-of-Order lzero n))
mere-equiv-number-of-semi-groups-of-order n =
  mere-equiv-number-of-connected-components
    ( is-π-finite-Semigroup-of-Order {lzero} zero-ℕ n)
```
