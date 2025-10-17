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
`X` of [cardinality](set-theory.cardinals.md) `n+1`, we can construct its
**complement**, which is a type of cardinality `n`.

## Definition

### The complement of a element in a `k`-element type of arbitrary universe level

```agda
isolated-element-Type-With-Cardinality-ℕ :
  {l : Level} (k : ℕ) (X : Type-With-Cardinality-ℕ l (succ-ℕ k)) →
  type-Type-With-Cardinality-ℕ (succ-ℕ k) X →
  isolated-element (type-Type-With-Cardinality-ℕ (succ-ℕ k) X)
pr1 (isolated-element-Type-With-Cardinality-ℕ k X x) = x
pr2 (isolated-element-Type-With-Cardinality-ℕ k X x) =
  has-decidable-equality-has-cardinality-ℕ
    ( succ-ℕ k)
    ( has-cardinality-type-Type-With-Cardinality-ℕ (succ-ℕ k) X)
    ( x)

type-complement-element-Type-With-Cardinality-ℕ :
  {l1 : Level} (k : ℕ) →
  Σ ( Type-With-Cardinality-ℕ l1 (succ-ℕ k))
    ( type-Type-With-Cardinality-ℕ (succ-ℕ k)) →
  UU l1
type-complement-element-Type-With-Cardinality-ℕ k (X , x) =
  complement-isolated-element
    ( type-Type-With-Cardinality-ℕ (succ-ℕ k) X)
    ( isolated-element-Type-With-Cardinality-ℕ k X x)

equiv-maybe-structure-element-Type-With-Cardinality-ℕ :
  {l : Level} (k : ℕ) (X : Type-With-Cardinality-ℕ l (succ-ℕ k)) →
  (x : type-Type-With-Cardinality-ℕ (succ-ℕ k) X) →
  Maybe (type-complement-element-Type-With-Cardinality-ℕ k (pair X x)) ≃
  type-Type-With-Cardinality-ℕ (succ-ℕ k) X
equiv-maybe-structure-element-Type-With-Cardinality-ℕ k X x =
  equiv-maybe-structure-isolated-element
    ( type-Type-With-Cardinality-ℕ (succ-ℕ k) X)
    ( isolated-element-Type-With-Cardinality-ℕ k X x)

has-cardinality-type-complement-element-Type-With-Cardinality-ℕ :
  {l1 : Level} (k : ℕ)
  (X :
    Σ ( Type-With-Cardinality-ℕ l1 (succ-ℕ k))
      ( type-Type-With-Cardinality-ℕ (succ-ℕ k))) →
  has-cardinality-ℕ k (type-complement-element-Type-With-Cardinality-ℕ k X)
has-cardinality-type-complement-element-Type-With-Cardinality-ℕ
  k (pair (pair X H) x) =
  apply-universal-property-trunc-Prop H
    ( has-cardinality-ℕ-Prop k
      ( type-complement-element-Type-With-Cardinality-ℕ k
        ( pair (pair X H) x)))
    ( λ e →
      unit-trunc-Prop
        ( equiv-equiv-Maybe
          ( ( inv-equiv
              ( equiv-maybe-structure-element-Type-With-Cardinality-ℕ k
                ( pair X H)
                ( x))) ∘e
            ( e))))

complement-element-Type-With-Cardinality-ℕ :
  {l1 : Level} (k : ℕ) →
  Σ ( Type-With-Cardinality-ℕ l1 (succ-ℕ k))
    ( type-Type-With-Cardinality-ℕ (succ-ℕ k)) →
  Type-With-Cardinality-ℕ l1 k
pr1 (complement-element-Type-With-Cardinality-ℕ k T) =
  type-complement-element-Type-With-Cardinality-ℕ k T
pr2 (complement-element-Type-With-Cardinality-ℕ k T) =
  has-cardinality-type-complement-element-Type-With-Cardinality-ℕ k T

inclusion-complement-element-Type-With-Cardinality-ℕ :
  {l1 : Level} (k : ℕ)
  (X :
    Σ ( Type-With-Cardinality-ℕ l1 (succ-ℕ k))
      ( type-Type-With-Cardinality-ℕ (succ-ℕ k))) →
  type-complement-element-Type-With-Cardinality-ℕ k X →
  type-Type-With-Cardinality-ℕ (succ-ℕ k) (pr1 X)
inclusion-complement-element-Type-With-Cardinality-ℕ k X x = pr1 x
```

### The action of equivalences on complements of isolated points

```agda
equiv-complement-element-Type-With-Cardinality-ℕ :
  {l1 : Level} (k : ℕ)
  (X Y :
    Σ ( Type-With-Cardinality-ℕ l1 (succ-ℕ k))
      ( type-Type-With-Cardinality-ℕ (succ-ℕ k))) →
  (e : equiv-Type-With-Cardinality-ℕ (succ-ℕ k) (pr1 X) (pr1 Y))
  (p : Id (map-equiv e (pr2 X)) (pr2 Y)) →
  equiv-Type-With-Cardinality-ℕ k
    ( complement-element-Type-With-Cardinality-ℕ k X)
    ( complement-element-Type-With-Cardinality-ℕ k Y)
equiv-complement-element-Type-With-Cardinality-ℕ
  k S T e p =
  equiv-complement-isolated-element e
    ( x , (λ x' → has-decidable-equality-has-cardinality-ℕ (succ-ℕ k) H x x'))
    ( y , (λ y' → has-decidable-equality-has-cardinality-ℕ (succ-ℕ k) K y y'))
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
