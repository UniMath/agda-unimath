# Finite monoids

```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-group-theory.finite-monoids where

open import elementary-number-theory.natural-numbers using (ℕ; succ-ℕ; zero-ℕ)

open import finite-group-theory.finite-semigroups using
  ( Semigroup-of-Order; is-π-finite-Semigroup-of-Order)

open import foundation.decidable-types using (is-decidable-prod)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_)
open import foundation.mere-equivalences using (mere-equiv)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop)
open import foundation.set-truncations using (type-trunc-Set)
open import foundation.type-arithmetic-dependent-pair-types using
  ( equiv-right-swap-Σ)
open import foundation.universe-levels using (Level; UU; lsuc; lzero)

open import group-theory.monoids using
  ( Monoid; type-Monoid; is-unital-Semigroup; is-unital-Semigroup-Prop)
open import group-theory.semigroups using (mul-Semigroup)

open import univalent-combinatorics.counting using
  ( has-decidable-equality-count)
open import univalent-combinatorics.decidable-dependent-function-types using
  ( is-decidable-Π-count)
open import univalent-combinatorics.decidable-dependent-pair-types using
  ( is-decidable-Σ-count)
open import univalent-combinatorics.finite-types using
  ( is-finite; is-finite-Prop; is-finite-is-decidable-Prop)
open import univalent-combinatorics.pi-finite-types using
  ( is-π-finite; is-π-finite-equiv; is-π-finite-Σ; is-π-finite-is-finite;
    number-of-connected-components; mere-equiv-number-of-connected-components)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

A finite monoid is a monoid of which the underlying type is finite.

## Definition

### Monoids of order n

```agda
Monoid-of-Order : (l : Level) (n : ℕ) → UU (lsuc l)
Monoid-of-Order l n = Σ (Monoid l) (λ M → mere-equiv (Fin n) (type-Monoid M))
```

## Properties

### For any semigroup of order n, the type of multiplicative units is finite

```agda
is-finite-is-unital-Semigroup :
  {l : Level} {n : ℕ} (X : Semigroup-of-Order l n) →
  is-finite (is-unital-Semigroup (pr1 X))
is-finite-is-unital-Semigroup {l} {n} X =
  apply-universal-property-trunc-Prop
    ( pr2 X)
    ( is-finite-Prop _)
    ( λ e →
      is-finite-is-decidable-Prop
        ( is-unital-Semigroup-Prop (pr1 X))
        ( is-decidable-Σ-count
          ( pair n e)
          ( λ u →
            is-decidable-prod
              ( is-decidable-Π-count
                ( pair n e)
                ( λ x →
                  has-decidable-equality-count
                    ( pair n e)
                    ( mul-Semigroup (pr1 X) u x)
                    ( x)))
              ( is-decidable-Π-count
                ( pair n e)
                ( λ x →
                  has-decidable-equality-count
                    ( pair n e)
                    ( mul-Semigroup (pr1 X) x u)
                    ( x))))))
```

### The type of monoids of order `n` is π-finite

```agda
is-π-finite-Monoid-of-Order :
  {l : Level} (k n : ℕ) → is-π-finite k (Monoid-of-Order l n)
is-π-finite-Monoid-of-Order {l} k n =
  is-π-finite-equiv k e
    ( is-π-finite-Σ k
      ( is-π-finite-Semigroup-of-Order (succ-ℕ k) n)
      ( λ X →
        is-π-finite-is-finite k
          ( is-finite-is-unital-Semigroup X)))
  where
  e : Monoid-of-Order l n ≃
      Σ (Semigroup-of-Order l n) (λ X → is-unital-Semigroup (pr1 X))
  e = equiv-right-swap-Σ
```

### The function that returns for any n the number of monoids of order n up to isomorphism

```agda
number-of-monoids-of-order : ℕ → ℕ
number-of-monoids-of-order n =
  number-of-connected-components
    ( is-π-finite-Monoid-of-Order {lzero} zero-ℕ n)

mere-equiv-number-of-monoids-of-order :
  (n : ℕ) →
  mere-equiv
    ( Fin (number-of-monoids-of-order n))
    ( type-trunc-Set (Monoid-of-Order lzero n))
mere-equiv-number-of-monoids-of-order n =
  mere-equiv-number-of-connected-components
    ( is-π-finite-Monoid-of-Order {lzero} zero-ℕ n)
```
