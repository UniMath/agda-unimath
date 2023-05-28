# Complements of isolated points of finite types

```agda
module univalent-combinatorics.complements-isolated-points where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-maybe
open import foundation.identity-types
open import foundation.isolated-points
open import foundation.maybe
open import foundation.propositional-truncations
open import foundation.universe-levels

open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

For any point `x` in a finite type `X` of cardinality `n+1`, we can construct
its complement, which is a type of cardinality `n`.

## Definition

### The complement of a point in a k-element type of arbitrary universe level

```agda
isolated-point-UU-Fin :
  {l : Level} (k : ℕ) (X : UU-Fin l (succ-ℕ k)) →
  type-UU-Fin (succ-ℕ k) X →
  isolated-point (type-UU-Fin (succ-ℕ k) X)
pr1 (isolated-point-UU-Fin k X x) = x
pr2 (isolated-point-UU-Fin k X x) =
  has-decidable-equality-has-cardinality
    ( succ-ℕ k)
    ( has-cardinality-type-UU-Fin (succ-ℕ k) X)
    ( x)

type-complement-point-UU-Fin :
  {l1 : Level} (k : ℕ) →
  Σ (UU-Fin l1 (succ-ℕ k)) (type-UU-Fin (succ-ℕ k)) → UU l1
type-complement-point-UU-Fin k (X , x) =
  complement-isolated-point
    ( type-UU-Fin (succ-ℕ k) X)
    ( isolated-point-UU-Fin k X x)

equiv-maybe-structure-point-UU-Fin :
  {l : Level} (k : ℕ) (X : UU-Fin l (succ-ℕ k)) →
  (x : type-UU-Fin (succ-ℕ k) X) →
  Maybe (type-complement-point-UU-Fin k (pair X x)) ≃
  type-UU-Fin (succ-ℕ k) X
equiv-maybe-structure-point-UU-Fin k X x =
  equiv-maybe-structure-isolated-point
    ( type-UU-Fin (succ-ℕ k) X)
    ( isolated-point-UU-Fin k X x)

has-cardinality-type-complement-point-UU-Fin :
  {l1 : Level} (k : ℕ)
  (X : Σ (UU-Fin l1 (succ-ℕ k)) (type-UU-Fin (succ-ℕ k))) →
  has-cardinality k (type-complement-point-UU-Fin k X)
has-cardinality-type-complement-point-UU-Fin k (pair (pair X H) x) =
  apply-universal-property-trunc-Prop H
    ( has-cardinality-Prop k
      ( type-complement-point-UU-Fin k (pair (pair X H) x)))
    ( λ e →
      unit-trunc-Prop
        ( equiv-equiv-Maybe
          ( ( inv-equiv
              ( equiv-maybe-structure-point-UU-Fin k (pair X H) x)) ∘e
            ( e))))

complement-point-UU-Fin :
  {l1 : Level} (k : ℕ) →
  Σ (UU-Fin l1 (succ-ℕ k)) (type-UU-Fin (succ-ℕ k)) →
  UU-Fin l1 k
pr1 (complement-point-UU-Fin k T) =
  type-complement-point-UU-Fin k T
pr2 (complement-point-UU-Fin k T) =
  has-cardinality-type-complement-point-UU-Fin k T

inclusion-complement-point-UU-Fin :
  {l1 : Level} (k : ℕ)
  (X : Σ (UU-Fin l1 (succ-ℕ k)) (type-UU-Fin (succ-ℕ k))) →
  type-complement-point-UU-Fin k X → type-UU-Fin (succ-ℕ k) (pr1 X)
inclusion-complement-point-UU-Fin k X x = pr1 x
```

### The action of equivalences on complements of isolated points

```agda
equiv-complement-point-UU-Fin :
  {l1 : Level} (k : ℕ)
  (X Y : Σ (UU-Fin l1 (succ-ℕ k)) (type-UU-Fin (succ-ℕ k))) →
  (e : equiv-UU-Fin (succ-ℕ k) (pr1 X) (pr1 Y))
  (p : Id (map-equiv e (pr2 X)) (pr2 Y)) →
  equiv-UU-Fin k
    ( complement-point-UU-Fin k X)
    ( complement-point-UU-Fin k Y)
equiv-complement-point-UU-Fin
  k S T e p =
  equiv-complement-isolated-point e
    ( pair x (λ x' → has-decidable-equality-has-cardinality (succ-ℕ k) H x x'))
    ( pair y (λ y' → has-decidable-equality-has-cardinality (succ-ℕ k) K y y'))
    ( p)
  where
  H = pr2 (pr1 S)
  x = pr2 S
  K = pr2 (pr1 T)
  y = pr2 T
```

## Properties

### The map from a pointed `k+1`-element type to the complement of the point is an equivalence

This remains to be shown.
