# Vectors of set quotients

```agda
{-# OPTIONS --lossy-unification #-}
```

```agda
module foundation.vectors-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.cartesian-products-set-quotients
open import foundation.coproduct-types
open import foundation.equality-cartesian-product-types
open import foundation.equational-reasoning
open import foundation.equivalence-classes
open import foundation.function-extensionality
open import foundation.functoriality-propositional-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.multivariable-operations
open import foundation.propositional-truncations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.unit-type
open import foundation.univalence

open import foundation-core.cartesian-product-types
open import foundation-core.dependent-pair-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.propositions
open import foundation-core.universe-levels

open import linear-algebra.vectors

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Say we have a family of types `A1`, ..., `An` each equipped with an equivalence
relation `Ri`. Then, the set quotient of a vector with these types is the vector
of the set quotients of each `Ai`.

## Definition

### The induced relation on the vector of types

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
     ( all-sim-Rel-Prop)
     ( pair
       ( is-reflexive-all-sim-Rel-Prop)
       ( pair
         ( is-symmetric-all-sim-Rel-Prop)
         ( is-transitive-all-sim-Rel-Prop)))
```

### The set quotient of a vector of types

```agda
  set-quotient-vector : UU (l1 ⊔ l2)
  set-quotient-vector =
    (i : Fin n) → set-quotient (Rs i)

  is-set-set-quotient-vector :
    is-set set-quotient-vector
  is-set-set-quotient-vector = is-set-Π (λ i → (is-set-set-quotient (Rs i)))

  set-quotient-vector-Set :
    Set (l1 ⊔ l2)
  pr1 set-quotient-vector-Set = set-quotient-vector
  pr2 set-quotient-vector-Set = is-set-set-quotient-vector

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

equiv-set-quotient-vector :
  { l1 l2 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( Rs : (i : Fin n) → Eq-Rel l2 (As i)) →
  set-quotient-vector n As Rs ≃ set-quotient (all-sim-Eq-Rel n As Rs)
equiv-set-quotient-vector zero-ℕ As Rs =
  pair
    ( λ a →
      ( quotient-map
        ( all-sim-Eq-Rel zero-ℕ As Rs)
        ( empty-multivariable-input As)))
    ( pair
      ( pair
        ( λ a → λ ())
        ( λ x →
          ( induction-set-quotient
            ( all-sim-Eq-Rel zero-ℕ As Rs)
            ( λ x → pair _ (is-set-set-quotient _ _ x))
            ( λ a → apply-effectiveness-quotient-map' _ λ ()) x)))
      ( pair
        ( λ a → λ ())
        ( λ x → eq-htpy λ ())))
equiv-set-quotient-vector (succ-ℕ n) As Rs =
  equivalence-reasoning
    set-quotient-vector (succ-ℕ n) As Rs
      ≃ set-quotient (Rs (inr star)) ×
          ( set-quotient-vector n
            ( tail-functional-vec n As)
            ( λ x → Rs (inl x)))
        by lemma
      ≃ set-quotient (Rs (inr star)) ×
          ( set-quotient
            ( all-sim-Eq-Rel n
              ( tail-functional-vec n As)
              ( λ x → Rs (inl x))))
        by equiv-eq
          ( ap
            ( _×_ (set-quotient (Rs (inr star))))
            ( eq-equiv _ _
              ( equiv-set-quotient-vector n
                ( tail-functional-vec n As)
                ( λ x → Rs (inl x)))))
      ≃ type-quotient-prod
          ( Rs (inr star))
          ( all-sim-Eq-Rel n
            ( tail-functional-vec n As)
            ( λ x → Rs (inl x)))
        by inv-equiv (equiv-quotient-prod-prod-set-quotient _ _)
      ≃ equivalence-class
          (prod-Eq-Rel
          ( Rs (inr star))
          ( all-sim-Eq-Rel n
            ( tail-functional-vec n As)
            ( λ x → Rs (inl x))))
        by inv-equiv (compute-set-quotient _)
      ≃ equivalence-class (all-sim-Eq-Rel (succ-ℕ n) As Rs)
        by equiv-prod-R0-Rs
      ≃ set-quotient (all-sim-Eq-Rel (succ-ℕ n) As Rs)
        by compute-set-quotient _
  where
  equivalence-class-prod-R0-Rs =
    equivalence-class
      ( prod-Eq-Rel
        ( Rs (inr star))
        ( all-sim-Eq-Rel n
          ( tail-functional-vec n As)
          ( λ x → Rs (inl x))))
  map-equivalence-classes :
    equivalence-class-prod-R0-Rs →
    equivalence-class (all-sim-Eq-Rel (succ-ℕ n) As Rs)
  map-equivalence-classes (P , H) =
    pair
      ( λ as →
        ( P (pair (as (inr star))
          ( tail-multivariable-input n As as))))
      ( map-trunc-Prop
        ( λ ((a , as) , p) →
          pair
          ( cons-multivariable-input' n As a as)
          ( λ a's →
            pair
              ( λ { h (inl x) →
                pr2
                  ( forward-implication
                    ( p
                      ( pair
                        ( a's (inr star))
                        ( tail-multivariable-input n As a's)))
                    ( h)) x;
                    h (inr star) →
                      pr1
                        ( forward-implication
                          ( p
                            ( pair
                              ( a's (inr star))
                              ( tail-multivariable-input n As a's)))
                          ( h))})
              ( λ h →
                ( backward-implication
                  ( p
                    ( pair
                      ( a's (inr star))
                      ( tail-multivariable-input n As a's))))
                ( pair
                  ( h (inr star))
                  ( λ i → h (inl i))))))
        ( H))
  inv-map-equivalence-classes :
    equivalence-class (all-sim-Eq-Rel (succ-ℕ n) As Rs) →
    equivalence-class-prod-R0-Rs
  inv-map-equivalence-classes (P , H) =
    pair
      ( λ (a , as) → P (cons-multivariable-input' n As a as))
      ( map-trunc-Prop
        ( λ (as , p) →
          pair
            ( pair (as (inr star)) (λ i → as (inl i)))
            ( λ (a' , a's) →
              pair
                ( λ h →
                  pair
                    ( forward-implication
                      ( p (cons-multivariable-input' n As a' a's))
                      ( h)
                      ( inr star))
                ( λ i →
                  forward-implication
                    ( p (cons-multivariable-input' n As a' a's))
                    ( h)
                    (inl i)))
                ( λ (R-a-a' , R-as-a's) →
                  backward-implication
                    ( p (cons-multivariable-input' n As a' a's))
                    ( λ { (inl x) → R-as-a's x;
                          (inr star) → R-a-a'}))))
        ( H))
  issec-map-equivalence-classes :
    ( map-equivalence-classes ∘
      inv-map-equivalence-classes) ~
    ( λ a → a)
  issec-map-equivalence-classes (P , H) =
    eq-pair-Σ
      ( eq-htpy
        ( λ as →
          ( eq-pair-Σ
            ( ap
              ( pr1 ∘ P)
              ( eq-htpy
                ( λ { (inl x) → refl;
                      (inr star) → refl})))
            ( eq-is-prop' (is-prop-is-prop _) _ _))))
      ( eq-is-prop' is-prop-type-trunc-Prop  _ _)
  isretr-map-equivalence-classes :
    ( inv-map-equivalence-classes ∘
      map-equivalence-classes) ~
    ( λ a → a)
  isretr-map-equivalence-classes (P , H) =
    eq-pair-Σ
      ( eq-htpy
        ( λ x →
          ( eq-pair-Σ
            ( refl)
            ( eq-is-prop' (is-prop-is-prop _) _ _))))
      ( eq-is-prop' is-prop-type-trunc-Prop _ _)
  equiv-prod-R0-Rs :
    equivalence-class-prod-R0-Rs ≃
    equivalence-class (all-sim-Eq-Rel (succ-ℕ n) As Rs)
  equiv-prod-R0-Rs =
    pair
      map-equivalence-classes
      ( pair
        ( pair
          inv-map-equivalence-classes
          issec-map-equivalence-classes)
        ( pair
          inv-map-equivalence-classes
          isretr-map-equivalence-classes))
  lemma :
    set-quotient-vector (succ-ℕ n) As Rs
      ≃ (set-quotient (Rs (inr star)) ×
          ( set-quotient-vector n
            ( tail-functional-vec n As)
            ( λ x → Rs (inl x))))
  lemma =
    pair
      ( λ {qas →
        ( pair
           ( qas (inr star))
           ( λ i → qas (inl i)))})
      ( pair
        ( pair
          ( λ { (qa , qas) (inl i) → qas i ;
                (qa , qas) (inr star) → qa})
          ( λ (qa , qas) → eq-pair-Σ refl refl))
        ( pair
          ( λ { (qa , qas) (inl i) → qas i ;
                (qa , qas) (inr star) → qa})
          ( λ qas →
            ( eq-htpy
              ( λ { (inl x) → refl ;
                    (inr star) → refl})))))
```
