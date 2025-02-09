# Decidable equivalence relations on finite types

```agda
module univalent-combinatorics.decidable-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.decidable-equality
open import foundation.decidable-equivalence-relations
open import foundation.decidable-relations
open import foundation.decidable-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-propositions
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.function-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.surjective-maps
```

</details>

## Idea

A **decidable equivalence relation** on a
[finite type](univalent-combinatorics.finite-types.md) is an
[equivalence relation](foundation-core.equivalence-relations.md) `R` such that
each `R x y` is a
[decidable proposition](foundation-core.decidable-propositions.md).

## Definition

```agda
Decidable-Equivalence-Relation-Finite-Type :
  {l1 : Level} (l2 : Level) (X : Finite-Type l1) → UU (l1 ⊔ lsuc l2)
Decidable-Equivalence-Relation-Finite-Type l2 X =
  Decidable-Equivalence-Relation l2 (type-Finite-Type X)

module _
  {l1 l2 : Level} (X : Finite-Type l1) (R : Decidable-Equivalence-Relation-Finite-Type l2 X)
  where

  decidable-relation-Decidable-Equivalence-Relation-Finite-Type :
    Decidable-Relation l2 (type-Finite-Type X)
  decidable-relation-Decidable-Equivalence-Relation-Finite-Type =
    decidable-relation-Decidable-Equivalence-Relation R

  relation-Decidable-Equivalence-Relation-Finite-Type :
    type-Finite-Type X → type-Finite-Type X → Prop l2
  relation-Decidable-Equivalence-Relation-Finite-Type =
    relation-Decidable-Equivalence-Relation R

  sim-Decidable-Equivalence-Relation-Finite-Type : type-Finite-Type X → type-Finite-Type X → UU l2
  sim-Decidable-Equivalence-Relation-Finite-Type =
    sim-Decidable-Equivalence-Relation R

  is-prop-sim-Decidable-Equivalence-Relation-Finite-Type :
    (x y : type-Finite-Type X) → is-prop (sim-Decidable-Equivalence-Relation-Finite-Type x y)
  is-prop-sim-Decidable-Equivalence-Relation-Finite-Type =
    is-prop-sim-Decidable-Equivalence-Relation R

  is-decidable-sim-Decidable-Equivalence-Relation-Finite-Type :
    (x y : type-Finite-Type X) → is-decidable (sim-Decidable-Equivalence-Relation-Finite-Type x y)
  is-decidable-sim-Decidable-Equivalence-Relation-Finite-Type =
    is-decidable-sim-Decidable-Equivalence-Relation R

  is-equivalence-relation-Decidable-Equivalence-Relation-Finite-Type :
    is-equivalence-relation relation-Decidable-Equivalence-Relation-Finite-Type
  is-equivalence-relation-Decidable-Equivalence-Relation-Finite-Type =
    is-equivalence-relation-Decidable-Equivalence-Relation R

  equivalence-relation-Decidable-Equivalence-Relation-Finite-Type :
    equivalence-relation l2 (type-Finite-Type X)
  equivalence-relation-Decidable-Equivalence-Relation-Finite-Type =
    equivalence-relation-Decidable-Equivalence-Relation R

  refl-Decidable-Equivalence-Relation-Finite-Type :
    is-reflexive sim-Decidable-Equivalence-Relation-Finite-Type
  refl-Decidable-Equivalence-Relation-Finite-Type =
    refl-Decidable-Equivalence-Relation R

  symmetric-Decidable-Equivalence-Relation-Finite-Type :
    is-symmetric sim-Decidable-Equivalence-Relation-Finite-Type
  symmetric-Decidable-Equivalence-Relation-Finite-Type =
    symmetric-Decidable-Equivalence-Relation R

  transitive-Decidable-Equivalence-Relation-Finite-Type :
    is-transitive sim-Decidable-Equivalence-Relation-Finite-Type
  transitive-Decidable-Equivalence-Relation-Finite-Type =
    transitive-Decidable-Equivalence-Relation R

module _
  {l1 l2 : Level} (A : Finite-Type l1) (R : Decidable-Relation l2 (type-Finite-Type A))
  where

  is-finite-relation-Decidable-Relation-Finite-Type :
    (x : type-Finite-Type A) → (y : type-Finite-Type A) → is-finite (rel-Decidable-Relation R x y)
  is-finite-relation-Decidable-Relation-Finite-Type x y =
    unit-trunc-Prop
      ( count-type-Decidable-Prop
        ( relation-Decidable-Relation R x y)
        ( is-decidable-Decidable-Relation R x y))

  is-finite-is-reflexive-Decidable-Relation-Prop-𝔽 :
    is-finite (is-reflexive-Relation-Prop (relation-Decidable-Relation R))
  is-finite-is-reflexive-Decidable-Relation-Prop-𝔽 =
    is-finite-Π
      ( is-finite-type-Finite-Type A)
      (λ x → is-finite-relation-Decidable-Relation-Finite-Type x x)

  is-finite-is-symmetric-Decidable-Relation-Prop-𝔽 :
    is-finite (is-symmetric-Relation-Prop (relation-Decidable-Relation R))
  is-finite-is-symmetric-Decidable-Relation-Prop-𝔽 =
    is-finite-Π
      ( is-finite-type-Finite-Type A)
      ( λ x →
        is-finite-Π
          ( is-finite-type-Finite-Type A)
          ( λ y →
            is-finite-function-type
              ( is-finite-relation-Decidable-Relation-Finite-Type x y)
              ( is-finite-relation-Decidable-Relation-Finite-Type y x)))

  is-finite-is-transitive-Decidable-Relation-Prop-𝔽 :
    is-finite (is-transitive-Relation-Prop (relation-Decidable-Relation R))
  is-finite-is-transitive-Decidable-Relation-Prop-𝔽 =
    is-finite-Π
      ( is-finite-type-Finite-Type A)
      ( λ x →
        is-finite-Π
          ( is-finite-type-Finite-Type A)
          ( λ y →
            is-finite-Π
              ( is-finite-type-Finite-Type A)
              ( λ z →
                is-finite-function-type
                  ( is-finite-relation-Decidable-Relation-Finite-Type y z)
                  ( is-finite-function-type
                    ( is-finite-relation-Decidable-Relation-Finite-Type x y)
                    ( is-finite-relation-Decidable-Relation-Finite-Type x z)))))

  is-finite-is-equivalence-Decidable-Relation-Prop-𝔽 :
    is-finite (is-equivalence-relation (relation-Decidable-Relation R))
  is-finite-is-equivalence-Decidable-Relation-Prop-𝔽 =
    is-finite-product
      ( is-finite-is-reflexive-Decidable-Relation-Prop-𝔽)
      ( is-finite-product
          is-finite-is-symmetric-Decidable-Relation-Prop-𝔽
          is-finite-is-transitive-Decidable-Relation-Prop-𝔽)
```

## Properties

#### The type of decidable equivalence relations on `A` is equivalent to the type of surjections from `A` into a finite type

```agda
equiv-Surjection-Finite-Type-Decidable-Equivalence-Relation-Finite-Type :
  {l1 : Level} (A : Finite-Type l1) →
  Decidable-Equivalence-Relation-Finite-Type l1 A ≃
  Surjection-Finite-Type l1 A
equiv-Surjection-Finite-Type-Decidable-Equivalence-Relation-Finite-Type {l1} A =
  ( equiv-Σ-equiv-base
      ( λ X → (type-Finite-Type A) ↠ (type-Finite-Type X))
      ( equiv-Σ
          ( is-finite)
          ( id-equiv)
          ( λ X →
            inv-equiv is-finite-iff-∃-surjection-has-decidable-equality)) ∘e
    ( ( inv-associative-Σ
          ( UU l1)
          ( λ X →
              has-decidable-equality X ×
              type-trunc-Prop (Σ ℕ (λ n → Fin n ↠ X)))
          ( λ X → type-Finite-Type A ↠ pr1 X)) ∘e
      ( ( equiv-Σ
            (λ X →
                Σ ( has-decidable-equality X ×
                    type-trunc-Prop (Σ ℕ (λ n → Fin n ↠ X)))
                  ( λ _ → pr1 A ↠ X))
            ( id-equiv)
            ( λ X →
              ( ( inv-equiv
                  ( associative-product
                    ( has-decidable-equality X)
                    ( type-trunc-Prop (Σ ℕ (λ n → Fin n ↠ X)))
                    ( type-Finite-Type A ↠ X))) ∘e
                ( ( equiv-product id-equiv commutative-product) ∘e
                  ( ( associative-product
                      ( has-decidable-equality (map-equiv id-equiv X))
                      ( type-Finite-Type A ↠ X)
                      ( type-trunc-Prop (Σ ℕ (λ n → Fin n ↠ X)))) ∘e
                  ( ( equiv-product commutative-product id-equiv) ∘e
                    ( ( equiv-add-redundant-prop
                        ( is-prop-type-trunc-Prop)
                        ( λ x →
                          apply-universal-property-trunc-Prop
                            ( is-finite-type-Finite-Type A)
                            ( trunc-Prop ( Σ ℕ (λ n → Fin n ↠ X)))
                            ( λ count-A →
                              unit-trunc-Prop
                                ( number-of-elements-count count-A ,
                                  ( ( map-surjection (pr1 x) ∘
                                      map-equiv-count count-A) ,
                                    is-surjective-right-comp-equiv
                                      ( is-surjective-map-surjection (pr1 x))
                                      ( equiv-count count-A)))))))))))) ∘e
        ( equiv-Surjection-Into-Set-Decidable-Equivalence-Relation
          ( type-Finite-Type A))))))
```

### The type of decidable equivalence relations on a finite type is finite

```agda
is-finite-Decidable-Relation-Finite-Type :
  {l1 : Level} (A : Finite-Type l1) →
  is-finite (Decidable-Relation l1 (type-Finite-Type A))
is-finite-Decidable-Relation-Finite-Type A =
  is-finite-Π
    ( is-finite-type-Finite-Type A)
    ( λ a →
      is-finite-Π
        ( is-finite-type-Finite-Type A)
        ( λ b → is-finite-Decidable-Prop))

is-finite-Decidable-Equivalence-Relation-Finite-Type :
  {l1 : Level} (A : Finite-Type l1) →
  is-finite (Decidable-Equivalence-Relation-Finite-Type l1 A)
is-finite-Decidable-Equivalence-Relation-Finite-Type A =
  is-finite-Σ
    ( is-finite-Decidable-Relation-Finite-Type A)
    ( is-finite-is-equivalence-Decidable-Relation-Prop-𝔽 A)
```

### The number of decidable equivalence relations on a finite type is a Stirling number of the second kind

This remains to be characterized.
[#745](https://github.com/UniMath/agda-unimath/issues/745)
