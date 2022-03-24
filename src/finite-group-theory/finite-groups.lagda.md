# Finite groups

```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-group-theory.finite-groups where

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

open import group-theory.groups using
  ( Group; type-Group; is-group; is-group-Prop)
open import group-theory.semigroups using (Semigroup; mul-Semigroup)

open import univalent-combinatorics.cartesian-product-types using (count-prod)
open import univalent-combinatorics.counting using
  ( has-decidable-equality-count)
open import univalent-combinatorics.counting-decidable-subtypes using (count-eq)
open import univalent-combinatorics.counting-dependent-function-types using
  ( count-Π)
open import univalent-combinatorics.counting-dependent-pair-types using
  ( count-Σ)
open import univalent-combinatorics.counting-function-types using
  ( count-function-type)
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

```agda
Group-of-Order : (l : Level) (n : ℕ) → UU (lsuc l)
Group-of-Order l n = Σ (Group l) (λ G → mere-equiv (Fin n) (type-Group G))

is-finite-is-group :
  {l : Level} {n : ℕ} (G : Semigroup-of-Order l n) →
  is-finite {l} (is-group (pr1 G))
is-finite-is-group {l} {n} G =
  apply-universal-property-trunc-Prop
    ( pr2 G)
    ( is-finite-Prop _)
    ( λ e →
      is-finite-is-decidable-Prop
        ( is-group-Prop (pr1 G))
        ( is-decidable-Σ-count
          ( count-Σ
            ( pair n e)
            ( λ u →
              count-prod
                ( count-Π
                  ( pair n e)
                  ( λ x →
                    count-eq
                      ( has-decidable-equality-count (pair n e))
                      ( mul-Semigroup (pr1 G) u x)
                      ( x)))
                ( count-Π
                  ( pair n e)
                  ( λ x →
                    count-eq
                      ( has-decidable-equality-count (pair n e))
                      ( mul-Semigroup (pr1 G) x u)
                      ( x)))))
          ( λ u →
            is-decidable-Σ-count
              ( count-function-type (pair n e) (pair n e))
              ( λ i →
                is-decidable-prod
                  ( is-decidable-Π-count
                    ( pair n e)
                    ( λ x →
                      has-decidable-equality-count
                        ( pair n e)
                        ( mul-Semigroup (pr1 G) (i x) x)
                        ( pr1 u)))
                  ( is-decidable-Π-count
                    ( pair n e)
                    ( λ x →
                      has-decidable-equality-count
                        ( pair n e)
                        ( mul-Semigroup (pr1 G) x (i x))
                        ( pr1 u)))))))

is-π-finite-Group-of-Order :
  {l : Level} (k n : ℕ) → is-π-finite k (Group-of-Order l n)
is-π-finite-Group-of-Order {l} k n =
  is-π-finite-equiv k e
    ( is-π-finite-Σ k
      ( is-π-finite-Semigroup-of-Order (succ-ℕ k) n)
      ( λ X →
        is-π-finite-is-finite k
          ( is-finite-is-group X)))
  where
  e : Group-of-Order l n ≃
      Σ (Semigroup-of-Order l n) (λ X → is-group (pr1 X))
  e = equiv-right-swap-Σ

number-of-groups-of-order : ℕ → ℕ
number-of-groups-of-order n =
  number-of-connected-components
    ( is-π-finite-Group-of-Order {lzero} zero-ℕ n)

mere-equiv-number-of-groups-of-order :
  (n : ℕ) →
  mere-equiv
    ( Fin (number-of-groups-of-order n))
    ( type-trunc-Set (Group-of-Order lzero n))
mere-equiv-number-of-groups-of-order n =
  mere-equiv-number-of-connected-components
    ( is-π-finite-Group-of-Order {lzero} zero-ℕ n)
```
