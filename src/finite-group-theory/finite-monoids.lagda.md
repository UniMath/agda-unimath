# Finite monoids

```agda
module finite-group-theory.finite-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.finite-semigroups

open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.set-truncations
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.monoids
open import group-theory.semigroups

open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-dependent-function-types
open import univalent-combinatorics.decidable-dependent-pair-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.pi-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

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
  {l : Level} (n : ℕ) (X : Semigroup-of-Order l n) →
  is-finite (is-unital-Semigroup (pr1 X))
is-finite-is-unital-Semigroup {l} n X =
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
          ( is-finite-is-unital-Semigroup n X)))
  where
  e :
    Monoid-of-Order l n ≃
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
