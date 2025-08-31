# Joins of finitely enumerable subtypes of elements in join-semilattices

```agda
module order-theory.joins-finitely-enumerable-subtypes-join-semilattices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.join-semilattices
open import order-theory.joins-finite-families-join-semilattices
open import order-theory.least-upper-bounds-posets

open import univalent-combinatorics.finitely-enumerable-subtypes
open import univalent-combinatorics.finitely-enumerable-types
```

</details>

## Idea

In a [join semilattice](order-theory.join-semilattices.md), the join of any
[inhabited](foundation.inhabited-subtypes.md)
[finitely enumerable subtype](univalent-combinatorics.finitely-enumerable-subtypes.md)
is its [least upper bound](order-theory.least-upper-bounds-posets.md).

## Definition

```agda
abstract
  has-least-upper-bound-inhabited-finite-enumeration-subtype-Order-Theoretic-Join-Semilattice :
    {l1 l2 l3 : Level} (X : Order-Theoretic-Join-Semilattice l1 l2) →
    (S : subtype l3 (type-Order-Theoretic-Join-Semilattice X)) →
    finite-enumeration-subtype S → is-inhabited-subtype S →
    has-least-upper-bound-subset-Poset
      ( poset-Order-Theoretic-Join-Semilattice X)
      ( S)
  has-least-upper-bound-inhabited-finite-enumeration-subtype-Order-Theoretic-Join-Semilattice
    X S eS@(zero-ℕ , _) |S| =
      ex-falso
        ( is-nonempty-is-inhabited
          ( |S|)
          ( is-empty-is-zero-finite-enumeration
            ( eS)
            ( refl)))
  has-least-upper-bound-inhabited-finite-enumeration-subtype-Order-Theoretic-Join-Semilattice
    X S eS@(succ-ℕ n , Fin-sn->>S) |S| =
      let
        (lub , is-lub-sequence) =
          has-least-upper-bound-join-fin-sequence-type-Order-Theoretic-Join-Semilattice
            ( X)
            ( n)
            ( pr1 ∘ map-surjection Fin-sn->>S)
        is-lub-subset :
          is-least-upper-bound-subset-Poset
            ( poset-Order-Theoretic-Join-Semilattice X)
            ( S)
            ( lub)
        is-lub-subset z =
          ( ( λ s≤z →
              forward-implication
                ( is-lub-sequence z)
                ( s≤z ∘ map-surjection Fin-sn->>S)) ,
            ( λ lub≤z s →
              let
                open
                  do-syntax-trunc-Prop
                    ( leq-Order-Theoretic-Join-Semilattice-Prop X (pr1 s) z)
                in do
                  (i , fi=s) ← is-surjective-map-surjection Fin-sn->>S s
                  tr
                    ( λ w → leq-Order-Theoretic-Join-Semilattice X (pr1 w) z)
                    ( fi=s)
                    ( backward-implication (is-lub-sequence z) lub≤z i)))
      in (lub , is-lub-subset)

module _
  {l1 l2 l3 : Level} (X : Order-Theoretic-Join-Semilattice l1 l2)
  (S : finitely-enumerable-subtype l3 (type-Order-Theoretic-Join-Semilattice X))
  (|S| : is-inhabited-finitely-enumerable-subtype S)
  where

  abstract
    has-least-upper-bound-inhabited-finitely-enumerable-subtype-Order-Theoretic-Join-Semilattice :
      has-least-upper-bound-subset-Poset
        ( poset-Order-Theoretic-Join-Semilattice X)
        ( subtype-finitely-enumerable-subtype S)
    has-least-upper-bound-inhabited-finitely-enumerable-subtype-Order-Theoretic-Join-Semilattice =
      rec-trunc-Prop
        ( has-least-upper-bound-subset-prop-Poset
          ( poset-Order-Theoretic-Join-Semilattice X)
          ( subtype-finitely-enumerable-subtype S))
        ( λ eS →
          has-least-upper-bound-inhabited-finite-enumeration-subtype-Order-Theoretic-Join-Semilattice
            ( X)
            ( subtype-finitely-enumerable-subtype S)
            ( eS)
            ( |S|))
          ( is-finitely-enumerable-subtype-finitely-enumerable-subtype S)

    join-inhabited-finitely-enumerable-subtype-Order-Theoretic-Join-Semilattice :
      type-Order-Theoretic-Join-Semilattice X
    join-inhabited-finitely-enumerable-subtype-Order-Theoretic-Join-Semilattice =
      pr1
        ( has-least-upper-bound-inhabited-finitely-enumerable-subtype-Order-Theoretic-Join-Semilattice)

    is-least-upper-bound-join-inhabited-finitely-enumerable-subtype-Order-Theoretic-Join-Semilattice :
      is-least-upper-bound-subset-Poset
        ( poset-Order-Theoretic-Join-Semilattice X)
        ( subtype-finitely-enumerable-subtype S)
        ( join-inhabited-finitely-enumerable-subtype-Order-Theoretic-Join-Semilattice)
    is-least-upper-bound-join-inhabited-finitely-enumerable-subtype-Order-Theoretic-Join-Semilattice =
      pr2
        ( has-least-upper-bound-inhabited-finitely-enumerable-subtype-Order-Theoretic-Join-Semilattice)
```
