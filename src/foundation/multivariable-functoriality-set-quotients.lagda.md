# Multivariable functoriality of set quotients

```agda
{-# OPTIONS --lossy-unification #-}
```

```agda
module foundation.multivariable-functoriality-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.multivariable-operations
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences

open import linear-algebra.vectors

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Say we have a family of types `A1`, ..., `An` each equipped with an equivalence
relation `Ri`, as well as a type `X` equipped with an equivalence relation `X`,
Then, any multivariable operation from the `Ai`s to the `X` that respects the
equivalence relations extends uniquely to a multivariable operation from the
`Ai/Ri`s to `X/S`.

## Definition

### n-ary hom of equivalence relation

```agda
module _
  { l1 l2 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( Rs : (i : Fin n) → Eq-Rel l2 (As i))
  where

  all-sim-Rel :
    ( as a's : multivariable-input n As) →
    UU l2
  all-sim-Rel as a's =
    (i : Fin n) →
    sim-Eq-Rel (Rs i) (as i) (a's i)

  is-prop-all-sim-Rel :
    ( as a's : multivariable-input n As) →
    is-prop (all-sim-Rel as a's)
  is-prop-all-sim-Rel as a's =
    is-prop-Π λ i → is-prop-sim-Eq-Rel (Rs i) (as i) (a's i)

  all-sim-Rel-Prop :
    ( as a's : multivariable-input n As) →
    Prop l2
  all-sim-Rel-Prop as a's =
    pair
     (all-sim-Rel as a's)
     (is-prop-all-sim-Rel as a's)

  is-reflexive-all-sim-Rel-Prop :
    is-reflexive-Rel-Prop all-sim-Rel-Prop
  is-reflexive-all-sim-Rel-Prop i = refl-Eq-Rel (Rs i)

  is-symmetric-all-sim-Rel-Prop :
    is-symmetric-Rel-Prop all-sim-Rel-Prop
  is-symmetric-all-sim-Rel-Prop p i =
    symm-Eq-Rel (Rs i) (p i)

  is-transitive-all-sim-Rel-Prop :
    is-transitive-Rel-Prop all-sim-Rel-Prop
  is-transitive-all-sim-Rel-Prop p q i =
    trans-Eq-Rel (Rs i) (p i) (q i)

  all-sim-Eq-Rel :
    ( Eq-Rel l2 (multivariable-input n As))
  all-sim-Eq-Rel =
    pair
     ( all-sim-Rel-Prop )
     ( pair
       ( is-reflexive-all-sim-Rel-Prop )
       ( pair
         ( is-symmetric-all-sim-Rel-Prop )
         ( is-transitive-all-sim-Rel-Prop )))

  set-quotient-vector : UU (l1 ⊔ l2)
  set-quotient-vector =
    (i : Fin n) → set-quotient (Rs i)

  is-set-qARs :
    is-set set-quotient-vector
  is-set-qARs = is-set-Π (λ i → (is-set-set-quotient (Rs i)))

  set-quotient-vector-Set :
    Set (l1 ⊔ l2)
  pr1 set-quotient-vector-Set = set-quotient-vector
  pr2 set-quotient-vector-Set = is-set-qARs

  quotient-vector-map :
    multivariable-input n As →
    set-quotient-vector
  quotient-vector-map as i =
    quotient-map (Rs i) (as i)

  reflects-quotient-vector-map :
    reflects-Eq-Rel all-sim-Eq-Rel quotient-vector-map
  reflects-quotient-vector-map p =
    eq-htpy (λ i → apply-effectiveness-quotient-map' (Rs i) (p i))

  reflecting-map-quotient-vector-map :
    reflecting-map-Eq-Rel all-sim-Eq-Rel set-quotient-vector
  pr1 reflecting-map-quotient-vector-map = quotient-vector-map
  pr2 reflecting-map-quotient-vector-map = reflects-quotient-vector-map

curry-once-multivariable-reflecting-map :
  { l l1 l2 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) (succ-ℕ n))
  ( Rs : (i : Fin (succ-ℕ n)) → Eq-Rel l2 (As i)) →
  ( X : Set l) →
  reflecting-map-Eq-Rel (all-sim-Eq-Rel (succ-ℕ n) As Rs) (type-Set X) →
  set-quotient (Rs (inr star)) →
  multivariable-input n (tail-functional-vec n As) →
  type-Set X
curry-once-multivariable-reflecting-map n As Rs X (f , H) qa as =
  inv-precomp-set-quotient (Rs (inr star)) X
    ( pair
        ( λ a → f (cons-multivariable-input' n As a as ))
        ( λ p →
          ( H λ { (inl x) → refl-Eq-Rel (Rs (inl x));
                  (inr star) → p})))
    ( qa)

inv-precomp-set-quotient-vector :
  { l l1 l2 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( Rs : (i : Fin n) → Eq-Rel l2 (As i)) →
  ( X : Set l) →
  reflecting-map-Eq-Rel (all-sim-Eq-Rel n As Rs) (type-Set X) →
  set-quotient-vector n As Rs → (type-Set X)
inv-precomp-set-quotient-vector zero-ℕ As Rs X (f , p) qas = f
  (empty-multivariable-input As)
inv-precomp-set-quotient-vector (succ-ℕ n) As Rs X (f , H) qas =
  inv-precomp-set-quotient-vector n
    ( tail-functional-vec n As)
    ( λ i → Rs (inl i))
    ( function-Set (set-quotient (Rs (inr star))) X)
    ( pair
      ( λ as qa →
        ( curry-once-multivariable-reflecting-map
          n As Rs X (f , H) qa as))
      ( λ {bs bs'} K → eq-htpy λ qa →
          htpy-eq
            ( ap (inv-precomp-set-quotient (Rs (inr star)) X)
            ( eq-pair-Σ
              ( eq-htpy
                ( λ a →
                  H λ { (inl x) → K x ;
                        (inr star) → refl-Eq-Rel (Rs (inr star))}))
            ( eq-is-prop'
              ( is-prop-reflects-Eq-Rel (Rs (inr star)) X _ ) _ _)))
            ( qa)))
    ( λ i → qas (inl i))
    ( qas (inr star))
```
