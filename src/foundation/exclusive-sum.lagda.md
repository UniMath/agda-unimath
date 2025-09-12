# Exclusive sums

```agda
module foundation.exclusive-sum where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.symmetric-operations
open import foundation.universal-quantification
open import foundation.universe-levels
open import foundation.unordered-pairs

open import foundation-core.cartesian-product-types
open import foundation-core.decidable-propositions
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.transport-along-identifications

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The {{#concept "exclusive sum" Disambiguation="of types" Agda=exclusive-sum}} of
two types `A` and `B`, is the type consisting of

- elements of `A` together with a proof that `B` is
  [empty](foundation-core.empty-types.md), or
- elements of `B` together with a proof that `A` is empty.

The
{{#concept "exclusive sum" Disambiguation="of propositions" Agda=exclusive-sum-Prop}}
of [propositions](foundation-core.propositions.md) `P` and `Q` is likewise the
[proposition](foundation-core.propositions.md) that `P` holds and `Q` does not
hold, or `P` does not hold and `Q` holds. The exclusive sum of two propositions
is equivalent to the
[exclusive disjunction](foundation.exclusive-disjunction.md), which is shown
there.

## Definitions

### The exclusive sum of types

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  exclusive-sum : UU (l1 ⊔ l2)
  exclusive-sum = (A × ¬ B) + (B × ¬ A)
```

### The exclusive sum of propositions

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  exclusive-sum-Prop : Prop (l1 ⊔ l2)
  exclusive-sum-Prop =
    coproduct-Prop
      ( P ∧ (¬' Q))
      ( Q ∧ (¬' P))
      ( λ p q → pr2 q (pr1 p))

  type-exclusive-sum-Prop : UU (l1 ⊔ l2)
  type-exclusive-sum-Prop = type-Prop exclusive-sum-Prop

  abstract
    is-prop-type-exclusive-sum-Prop : is-prop type-exclusive-sum-Prop
    is-prop-type-exclusive-sum-Prop = is-prop-type-Prop exclusive-sum-Prop
```

### The canonical inclusion of the exclusive sum into the coproduct

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-coproduct-exclusive-sum : exclusive-sum A B → A + B
  map-coproduct-exclusive-sum (inl (a , _)) = inl a
  map-coproduct-exclusive-sum (inr (b , _)) = inr b
```

### The symmetric operation of exclusive sum

```agda
predicate-symmetric-exclusive-sum :
  {l : Level} (p : unordered-pair (UU l)) → type-unordered-pair p → UU l
predicate-symmetric-exclusive-sum p x =
  ( element-unordered-pair p x) × (¬ (other-element-unordered-pair p x))

symmetric-exclusive-sum : {l : Level} → symmetric-operation (UU l) (UU l)
symmetric-exclusive-sum p =
  Σ (type-unordered-pair p) (predicate-symmetric-exclusive-sum p)
```

### The symmetric operation of the exclusive sum of propositions

```agda
predicate-symmetric-exclusive-sum-Prop :
  {l : Level} (p : unordered-pair (Prop l)) →
  type-unordered-pair p → UU l
predicate-symmetric-exclusive-sum-Prop p =
  predicate-symmetric-exclusive-sum (map-unordered-pair type-Prop p)

type-symmetric-exclusive-sum-Prop :
  {l : Level} → symmetric-operation (Prop l) (UU l)
type-symmetric-exclusive-sum-Prop p =
  symmetric-exclusive-sum (map-unordered-pair type-Prop p)

all-elements-equal-type-symmetric-exclusive-sum-Prop :
  {l : Level} (p : unordered-pair (Prop l)) →
  all-elements-equal (type-symmetric-exclusive-sum-Prop p)
all-elements-equal-type-symmetric-exclusive-sum-Prop (X , P) x y =
  cases-is-prop-type-symmetric-exclusive-sum-Prop
    ( has-decidable-equality-is-finite
      ( is-finite-type-Type-With-Cardinality-ℕ 2 X)
      ( pr1 x)
      ( pr1 y))
  where
  cases-is-prop-type-symmetric-exclusive-sum-Prop :
    is-decidable (pr1 x ＝ pr1 y) → x ＝ y
  cases-is-prop-type-symmetric-exclusive-sum-Prop (inl p) =
    eq-pair-Σ
      ( p)
      ( eq-is-prop
        ( is-prop-product-Prop
          ( P (pr1 y))
          ( neg-type-Prop
            ( other-element-unordered-pair
              ( map-unordered-pair (type-Prop) (X , P))
              ( pr1 y)))))
  cases-is-prop-type-symmetric-exclusive-sum-Prop (inr np) =
    ex-falso
      ( tr
        ( λ z → ¬ (type-Prop (P z)))
        ( compute-swap-2-Element-Type X (pr1 x) (pr1 y) np)
        ( pr2 (pr2 x))
        ( pr1 (pr2 y)))

is-prop-type-symmetric-exclusive-sum-Prop :
  {l : Level} (p : unordered-pair (Prop l)) →
  is-prop (type-symmetric-exclusive-sum-Prop p)
is-prop-type-symmetric-exclusive-sum-Prop p =
  is-prop-all-elements-equal
    ( all-elements-equal-type-symmetric-exclusive-sum-Prop p)

symmetric-exclusive-sum-Prop :
  {l : Level} → symmetric-operation (Prop l) (Prop l)
pr1 (symmetric-exclusive-sum-Prop E) = type-symmetric-exclusive-sum-Prop E
pr2 (symmetric-exclusive-sum-Prop E) =
  is-prop-type-symmetric-exclusive-sum-Prop E
```

## Properties

### The symmetric exclusive sum at a standard unordered pair

```agda
module _
  {l : Level} {A B : UU l}
  where

  exclusive-sum-symmetric-exclusive-sum :
    symmetric-exclusive-sum (standard-unordered-pair A B) → exclusive-sum A B
  exclusive-sum-symmetric-exclusive-sum (pair (inl (inr _)) (p , nq)) =
    inl
      ( pair p
        ( tr
          ( λ t → ¬ (element-unordered-pair (standard-unordered-pair A B) t))
          ( compute-swap-Fin-2 (zero-Fin 1))
          ( nq)))
  exclusive-sum-symmetric-exclusive-sum (pair (inr _) (q , np)) =
    inr
      ( pair
        ( q)
        ( tr
          ( λ t → ¬ (element-unordered-pair (standard-unordered-pair A B) t))
          ( compute-swap-Fin-2 (one-Fin 1))
          ( np)))

  symmetric-exclusive-sum-exclusive-sum :
    exclusive-sum A B → symmetric-exclusive-sum (standard-unordered-pair A B)
  pr1 (symmetric-exclusive-sum-exclusive-sum (inl (a , nb))) = (zero-Fin 1)
  pr1 (pr2 (symmetric-exclusive-sum-exclusive-sum (inl (a , nb)))) = a
  pr2 (pr2 (symmetric-exclusive-sum-exclusive-sum (inl (a , nb)))) =
    tr
      ( λ t → ¬ (element-unordered-pair (standard-unordered-pair A B) t))
      ( inv (compute-swap-Fin-2 (zero-Fin 1)))
      ( nb)
  pr1 (symmetric-exclusive-sum-exclusive-sum (inr (na , b))) = (one-Fin 1)
  pr1 (pr2 (symmetric-exclusive-sum-exclusive-sum (inr (b , na)))) = b
  pr2 (pr2 (symmetric-exclusive-sum-exclusive-sum (inr (b , na)))) =
    tr
      ( λ t → ¬ (element-unordered-pair (standard-unordered-pair A B) t))
      ( inv (compute-swap-Fin-2 (one-Fin 1)))
      ( na)
```

```text
  eq-equiv-Prop
    ( ( ( equiv-coproduct
          ( ( ( left-unit-law-coproduct (type-Prop (P ∧ (¬' Q)))) ∘e
              ( equiv-coproduct
                ( left-absorption-Σ
                  ( λ x →
                    ( type-Prop
                      ( pr2 (standard-unordered-pair P Q) (inl (inl x)))) ×
                      ( ¬ ( type-Prop
                            ( pr2
                              ( standard-unordered-pair P Q)
                              ( map-swap-2-Element-Type
                                ( pr1 (standard-unordered-pair P Q))
                                ( inl (inl x))))))))
                ( ( equiv-product
                    ( id-equiv)
                    ( tr
                      ( λ b →
                        ( ¬ (type-Prop (pr2 (standard-unordered-pair P Q) b))) ≃
                        ( ¬ (type-Prop Q)))
                      ( inv (compute-swap-Fin-2 (zero-Fin ?)))
                      ( id-equiv))) ∘e
                    ( left-unit-law-Σ
                      ( λ y →
                        ( type-Prop
                          ( pr2 (standard-unordered-pair P Q) (inl (inr y)))) ×
                        ( ¬ ( type-Prop
                              ( pr2
                                ( standard-unordered-pair P Q)
                                ( map-swap-2-Element-Type
                                  ( pr1 (standard-unordered-pair P Q))
                                  ( inl (inr y))))))))))) ∘e
          ( ( right-distributive-Σ-coproduct
              ( λ x →
                ( type-Prop (pr2 (standard-unordered-pair P Q) (inl x))) ×
                ( ¬ ( type-Prop
                      ( pr2
                        ( standard-unordered-pair P Q)
                        ( map-swap-2-Element-Type
                          ( pr1 (standard-unordered-pair P Q)) (inl x)))))))))
        ( ( equiv-product
            ( tr
              ( λ b →
                ¬ (type-Prop (pr2 (standard-unordered-pair P Q) b)) ≃
                ¬ (type-Prop P))
              ( inv (compute-swap-Fin-2 (one-Fin ?)))
              ( id-equiv))
            ( id-equiv)) ∘e
          ( ( commutative-product) ∘e
            ( left-unit-law-Σ
              ( λ y →
                ( type-Prop (pr2 (standard-unordered-pair P Q) (inr y))) ×
                ( ¬ ( type-Prop
                      ( pr2
                        ( standard-unordered-pair P Q)
                        ( map-swap-2-Element-Type
                          ( pr1 (standard-unordered-pair P Q))
                          ( inr y)))))))))) ∘e
      ( right-distributive-Σ-coproduct
        ( λ x →
          ( type-Prop (pr2 (standard-unordered-pair P Q) x)) ×
          ( ¬ ( type-Prop
                ( pr2
                  ( standard-unordered-pair P Q)
                  ( map-swap-2-Element-Type
                    ( pr1 (standard-unordered-pair P Q))
                    ( x)))))))))
```

```agda
module _
  {l : Level} (P Q : Prop l)
  where

  exclusive-sum-symmetric-exclusive-sum-Prop :
    type-hom-Prop
      ( symmetric-exclusive-sum-Prop (standard-unordered-pair P Q))
      ( exclusive-sum-Prop P Q)
  exclusive-sum-symmetric-exclusive-sum-Prop (pair (inl (inr _)) (p , nq)) =
    inl
      ( pair p
        ( tr
          ( λ t →
            ¬ ( type-Prop
                ( element-unordered-pair (standard-unordered-pair P Q) t)))
          ( compute-swap-Fin-2 (zero-Fin 1))
          ( nq)))
  exclusive-sum-symmetric-exclusive-sum-Prop (pair (inr _) (q , np)) =
    inr
      ( pair q
        ( tr
          ( λ t →
            ¬ ( type-Prop
                ( element-unordered-pair (standard-unordered-pair P Q) t)))
          ( compute-swap-Fin-2 (one-Fin 1))
          ( np)))

  symmetric-exclusive-sum-exclusive-sum-Prop :
    type-hom-Prop
      ( exclusive-sum-Prop P Q)
      ( symmetric-exclusive-sum-Prop (standard-unordered-pair P Q))
  pr1 (symmetric-exclusive-sum-exclusive-sum-Prop (inl (p , nq))) = zero-Fin 1
  pr1 (pr2 (symmetric-exclusive-sum-exclusive-sum-Prop (inl (p , nq)))) = p
  pr2 (pr2 (symmetric-exclusive-sum-exclusive-sum-Prop (inl (p , nq)))) =
    tr
      ( λ t →
        ¬ (type-Prop (element-unordered-pair (standard-unordered-pair P Q) t)))
      ( inv (compute-swap-Fin-2 (zero-Fin 1)))
      ( nq)
  pr1 (symmetric-exclusive-sum-exclusive-sum-Prop (inr (q , np))) = one-Fin 1
  pr1 (pr2 (symmetric-exclusive-sum-exclusive-sum-Prop (inr (q , np)))) = q
  pr2 (pr2 (symmetric-exclusive-sum-exclusive-sum-Prop (inr (q , np)))) =
    tr
      ( λ t →
        ¬ (type-Prop (element-unordered-pair (standard-unordered-pair P Q) t)))
      ( inv (compute-swap-Fin-2 (one-Fin 1)))
      ( np)

eq-commmutative-exclusive-sum-exclusive-sum :
  {l : Level} (P Q : Prop l) →
  symmetric-exclusive-sum-Prop (standard-unordered-pair P Q) ＝
  exclusive-sum-Prop P Q
eq-commmutative-exclusive-sum-exclusive-sum P Q =
  eq-iff
    ( exclusive-sum-symmetric-exclusive-sum-Prop P Q)
    ( symmetric-exclusive-sum-exclusive-sum-Prop P Q)
```

### The exclusive sum of decidable types is decidable

```agda
is-decidable-exclusive-sum :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (exclusive-sum A B)
is-decidable-exclusive-sum d e =
  is-decidable-coproduct
    ( is-decidable-product d (is-decidable-neg e))
    ( is-decidable-product e (is-decidable-neg d))

module _
  {l1 l2 : Level} (P : Decidable-Prop l1) (Q : Decidable-Prop l2)
  where

  is-decidable-exclusive-sum-Decidable-Prop :
    is-decidable
      ( type-exclusive-sum-Prop (prop-Decidable-Prop P) (prop-Decidable-Prop Q))
  is-decidable-exclusive-sum-Decidable-Prop =
      is-decidable-coproduct
      ( is-decidable-product
        ( is-decidable-Decidable-Prop P)
        ( is-decidable-neg (is-decidable-Decidable-Prop Q)))
      ( is-decidable-product
        ( is-decidable-Decidable-Prop Q)
        ( is-decidable-neg (is-decidable-Decidable-Prop P)))

  exclusive-sum-Decidable-Prop : Decidable-Prop (l1 ⊔ l2)
  pr1 exclusive-sum-Decidable-Prop =
    type-exclusive-sum-Prop (prop-Decidable-Prop P) (prop-Decidable-Prop Q)
  pr1 (pr2 exclusive-sum-Decidable-Prop) =
    is-prop-type-exclusive-sum-Prop
      ( prop-Decidable-Prop P)
      ( prop-Decidable-Prop Q)
  pr2 (pr2 exclusive-sum-Decidable-Prop) =
    is-decidable-exclusive-sum-Decidable-Prop
```

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}
