# Complements of isolated elements of finite types

```agda
module univalent-combinatorics.complements-isolated-elements where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-maybe
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.maybe
open import foundation.propositional-truncations
open import foundation.universe-levels

open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

For any element `x` in a [finite type](univalent-combinatorics.finite-types.md)
`X` of [cardinality](set-theory.cardinalities.md) `n+1`, we can construct its
**complement**, which is a type of cardinality `n`.

## Definition

### The complement of a element in a `k`-element type of arbitrary universe level

```agda
isolated-element-Type-With-Finite-Cardinality :
  {l : Level} (k : ℕ) (X : Type-With-Finite-Cardinality l (succ-ℕ k)) →
  type-Type-With-Finite-Cardinality (succ-ℕ k) X →
  isolated-element (type-Type-With-Finite-Cardinality (succ-ℕ k) X)
pr1 (isolated-element-Type-With-Finite-Cardinality k X x) = x
pr2 (isolated-element-Type-With-Finite-Cardinality k X x) =
  has-decidable-equality-has-cardinality
    ( succ-ℕ k)
    ( has-cardinality-type-Type-With-Finite-Cardinality (succ-ℕ k) X)
    ( x)

type-complement-element-Type-With-Finite-Cardinality :
  {l1 : Level} (k : ℕ) →
  Σ (Type-With-Finite-Cardinality l1 (succ-ℕ k)) (type-Type-With-Finite-Cardinality (succ-ℕ k)) → UU l1
type-complement-element-Type-With-Finite-Cardinality k (X , x) =
  complement-isolated-element
    ( type-Type-With-Finite-Cardinality (succ-ℕ k) X)
    ( isolated-element-Type-With-Finite-Cardinality k X x)

equiv-maybe-structure-element-Type-With-Finite-Cardinality :
  {l : Level} (k : ℕ) (X : Type-With-Finite-Cardinality l (succ-ℕ k)) →
  (x : type-Type-With-Finite-Cardinality (succ-ℕ k) X) →
  Maybe (type-complement-element-Type-With-Finite-Cardinality k (pair X x)) ≃
  type-Type-With-Finite-Cardinality (succ-ℕ k) X
equiv-maybe-structure-element-Type-With-Finite-Cardinality k X x =
  equiv-maybe-structure-isolated-element
    ( type-Type-With-Finite-Cardinality (succ-ℕ k) X)
    ( isolated-element-Type-With-Finite-Cardinality k X x)

has-cardinality-type-complement-element-Type-With-Finite-Cardinality :
  {l1 : Level} (k : ℕ)
  (X : Σ (Type-With-Finite-Cardinality l1 (succ-ℕ k)) (type-Type-With-Finite-Cardinality (succ-ℕ k))) →
  has-cardinality k (type-complement-element-Type-With-Finite-Cardinality k X)
has-cardinality-type-complement-element-Type-With-Finite-Cardinality k (pair (pair X H) x) =
  apply-universal-property-trunc-Prop H
    ( has-cardinality-Prop k
      ( type-complement-element-Type-With-Finite-Cardinality k (pair (pair X H) x)))
    ( λ e →
      unit-trunc-Prop
        ( equiv-equiv-Maybe
          ( ( inv-equiv
              ( equiv-maybe-structure-element-Type-With-Finite-Cardinality k (pair X H) x)) ∘e
            ( e))))

complement-element-Type-With-Finite-Cardinality :
  {l1 : Level} (k : ℕ) →
  Σ (Type-With-Finite-Cardinality l1 (succ-ℕ k)) (type-Type-With-Finite-Cardinality (succ-ℕ k)) →
  Type-With-Finite-Cardinality l1 k
pr1 (complement-element-Type-With-Finite-Cardinality k T) =
  type-complement-element-Type-With-Finite-Cardinality k T
pr2 (complement-element-Type-With-Finite-Cardinality k T) =
  has-cardinality-type-complement-element-Type-With-Finite-Cardinality k T

inclusion-complement-element-Type-With-Finite-Cardinality :
  {l1 : Level} (k : ℕ)
  (X : Σ (Type-With-Finite-Cardinality l1 (succ-ℕ k)) (type-Type-With-Finite-Cardinality (succ-ℕ k))) →
  type-complement-element-Type-With-Finite-Cardinality k X → type-Type-With-Finite-Cardinality (succ-ℕ k) (pr1 X)
inclusion-complement-element-Type-With-Finite-Cardinality k X x = pr1 x
```

### The action of equivalences on complements of isolated points

```agda
equiv-complement-element-Type-With-Finite-Cardinality :
  {l1 : Level} (k : ℕ)
  (X Y : Σ (Type-With-Finite-Cardinality l1 (succ-ℕ k)) (type-Type-With-Finite-Cardinality (succ-ℕ k))) →
  (e : equiv-Type-With-Finite-Cardinality (succ-ℕ k) (pr1 X) (pr1 Y))
  (p : Id (map-equiv e (pr2 X)) (pr2 Y)) →
  equiv-Type-With-Finite-Cardinality k
    ( complement-element-Type-With-Finite-Cardinality k X)
    ( complement-element-Type-With-Finite-Cardinality k Y)
equiv-complement-element-Type-With-Finite-Cardinality
  k S T e p =
  equiv-complement-isolated-element e
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

### The map from a pointed `k+1`-element type to the complement of the element is an equivalence

This remains to be shown.
[#744](https://github.com/UniMath/agda-unimath/issues/744)
