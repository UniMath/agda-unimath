# Composition of species of subuniverse

```agda
module species.composition-species-of-subuniverse where
<<<<<<< HEAD

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.propositional-truncations
=======
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
open import foundation.raising-universe-levels
open import foundation.relaxed-sigma-decompositions
open import foundation.sigma-decomposition-subuniverse
open import foundation.small-types
open import foundation.subuniverses
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.univalence
<<<<<<< HEAD
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels
open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.decidable-propositions
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-sum-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
open import species.large-composition-species-of-types
open import univalent-combinatorics.sigma-decompositions
open import univalent-combinatorics.small-types
open import species.species-of-types-in-subuniverse
open import species.species-of-types
```

=======
open import foundation.universe-levels

open import species.large-composition-species-of-types
open import species.species-of-types-in-subuniverse
```

</details>

>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
## Idea

A species `S : Inhabited-Type → UU l` can be thought of as the analytic
endofunctor

```md
  X ↦ Σ (A : Inhabited-Type) (S A) × (A → X)
```

Using the formula for composition of analytic endofunctors, we obtain a way to
compose species.

## Definition

### Analytic composition of species

```agda
module _
  {l1 : Level} (l2 : Level)
  (P : subuniverse l1 l1 )
  (Q : subuniverse (l1 ⊔ l2) (l1 ⊔ l2))
  (S T : species-subuniverse P Q )
  where

  analytic-comp-species-subuniverse' :
    type-subuniverse P → UU (lsuc l1 ⊔ l2)
  analytic-comp-species-subuniverse' X =
<<<<<<< HEAD
    Σ ( Σ-Decomposition-subuniverse P (inclusion-subuniverse P X))
      ( λ D →
        ( inclusion-subuniverse
          ( Q)
          ( S (subuniverse-indexing-type-Σ-Decomposition-subuniverse P D))) ×
        ( (x : indexing-type-Σ-Decomposition-subuniverse P D ) →
          inclusion-subuniverse
          ( Q)
          ( T (subuniverse-cotype-Σ-Decomposition-subuniverse P D x))))
=======
    Σ ( Σ-Decomposition-subuniverse P X)
      ( λ D →
        ( inclusion-subuniverse
          ( Q)
          ( S (subuniverse-indexing-type-Σ-Decomposition-subuniverse P X D))) ×
        ( (x : indexing-type-Σ-Decomposition-subuniverse P X D ) →
          inclusion-subuniverse
          ( Q)
          ( T (subuniverse-cotype-Σ-Decomposition-subuniverse P X D x))))
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3

module _
  {l1 : Level} (l2 : Level)
  (P : subuniverse l1 l1 )
  (Q : subuniverse (l1 ⊔ l2) (l1 ⊔ l2))
  (C1 :
    ( S T : species-subuniverse P Q ) → (X : type-subuniverse P) →
    is-small (l1 ⊔ l2) (analytic-comp-species-subuniverse' l2 P Q S T X))
  (C2 :
    ( S T : species-subuniverse P Q ) → (X : type-subuniverse P) →
    ( is-in-subuniverse Q (type-is-small (C1 S T X))))
  (C3 :
    ( ( X : type-subuniverse P) →
      ( Y : (inclusion-subuniverse P X) → type-subuniverse P) →
      is-in-subuniverse P
        ( Σ (inclusion-subuniverse P X) (λ x → inclusion-subuniverse P (Y x)))))
  where

  analytic-comp-species-subuniverse :
    species-subuniverse P Q →
    species-subuniverse P Q →
    species-subuniverse P Q
  analytic-comp-species-subuniverse S T X =
    type-is-small (C1 S T X) , C2 S T X
```

## Properties

### Equivalent form with species of types

```agda
  equiv-Σ-extension-species-subuniverse :
    ( S : species-subuniverse P Q) ( X : type-subuniverse P) →
    inclusion-subuniverse Q (S X) ≃
    Σ-extension-species-subuniverse P Q S (inclusion-subuniverse P X)
  equiv-Σ-extension-species-subuniverse S X =
    inv-left-unit-law-Σ-is-contr
      ( is-proof-irrelevant-is-prop
        ( is-subtype-subuniverse P (inclusion-subuniverse P X))
        ( pr2 X))
      ( pr2 X)

  equiv-analytic-comp-extension-species-subuniverse :
    ( S : species-subuniverse P Q)
    ( T : species-subuniverse P Q)
    ( X : UU l1) →
    Σ-extension-species-subuniverse P Q
      ( analytic-comp-species-subuniverse S T)
      ( X) ≃
    ( analytic-comp-species-types
      ( Σ-extension-species-subuniverse P Q S)
      ( Σ-extension-species-subuniverse P Q T)
      ( X))
  equiv-analytic-comp-extension-species-subuniverse S T X =
    ( ( equiv-tot
        ( λ D →
          ( ( equiv-prod id-equiv (inv-equiv distributive-Π-Σ)) ∘e
          ( ( inv-equiv right-distributive-prod-Σ) ∘e
          ( ( equiv-tot (λ _ → inv-equiv (left-distributive-prod-Σ)))))) ∘e
          ( ( assoc-Σ _ _ _)))) ∘e
<<<<<<< HEAD
    ( ( assoc-Σ
        ( Relaxed-Σ-Decomposition l1 l1 X)
        ( λ D →
            is-in-subuniverse P (indexing-type-Relaxed-Σ-Decomposition D) ×
            ((x : indexing-type-Relaxed-Σ-Decomposition D) →
             is-in-subuniverse P (cotype-Relaxed-Σ-Decomposition D x)))
        ( _)) ∘e
    ( ( equiv-Σ-equiv-base
        ( _)
        ( equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse P ∘e
          ( inv-equiv
            ( equiv-add-redundant-prop
              ( is-prop-type-Prop (P X))
              ( λ D →
                ( tr
                  ( is-in-subuniverse P)
                  ( eq-equiv _ _
                    ( inv-equiv
                      ( matching-correspondence-Σ-Decomposition-subuniverse
                        P
                        D)))
                  ( C3
                    ( subuniverse-indexing-type-Σ-Decomposition-subuniverse P D)
                    ( subuniverse-cotype-Σ-Decomposition-subuniverse P D))))) ∘e
                commutative-prod))) ∘e
    ( ( inv-assoc-Σ
        ( is-in-subuniverse P X)
        ( λ a → Σ-Decomposition-subuniverse P X)
        ( _)) ∘e
    ( ( equiv-tot (λ p → inv-equiv (equiv-is-small (C1 S T (X , p))))))))))
=======
      ( ( assoc-Σ
          ( Relaxed-Σ-Decomposition l1 l1 X)
          ( λ D →
              is-in-subuniverse P (indexing-type-Relaxed-Σ-Decomposition D) ×
              ((x : indexing-type-Relaxed-Σ-Decomposition D) →
               is-in-subuniverse P (cotype-Relaxed-Σ-Decomposition D x)))
          ( _)) ∘e
        ( ( equiv-Σ-equiv-base
            ( _)
            ( ( inv-equiv
                ( equiv-add-redundant-prop
                  ( is-prop-type-Prop (P X))
                  ( λ D →
                    ( tr
                      ( is-in-subuniverse P)
                      ( eq-equiv
                        ( Σ (indexing-type-Relaxed-Σ-Decomposition (pr1 D))
                          (cotype-Relaxed-Σ-Decomposition (pr1 D)))
                        ( X)
                        ( inv-equiv
                          ( matching-correspondence-Relaxed-Σ-Decomposition
                            (pr1 D))))
                      ( C3
                        ( indexing-type-Relaxed-Σ-Decomposition (pr1 D) ,
                          pr1 (pr2 D))
                        ( λ x →
                          ( cotype-Relaxed-Σ-Decomposition (pr1 D) x ,
                            pr2 (pr2 D) x)))))) ∘e
              ( commutative-prod ∘e
              ( equiv-tot
                ( λ p →
                  equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse
                    ( P)
                    (X , p))))))) ∘e
          ( ( inv-assoc-Σ
              ( is-in-subuniverse P X)
              ( λ p → Σ-Decomposition-subuniverse P (X , p))
              ( _)) ∘e
            ( ( equiv-tot
                ( λ p → inv-equiv (equiv-is-small (C1 S T (X , p))))))))))
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
```

### Unit laws for analytic composition of species-subuniverse

```agda
  module _
    (C4 : is-in-subuniverse P (raise-unit l1))
    (C5 :
<<<<<<< HEAD
      ( X : type-subuniverse P) →
      ( is-in-subuniverse
          ( Q)
          ( type-is-small
            ( is-small-lmax l2 ( is-contr (inclusion-subuniverse P X))))))
=======
    ( X : type-subuniverse P) →
    ( is-in-subuniverse
    ( Q)
    ( type-is-small
    ( is-small-lmax l2 ( is-contr (inclusion-subuniverse P X))))))
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
    where

    analytic-unit-species-subuniverse :
      species-subuniverse P Q
    analytic-unit-species-subuniverse X =
      type-is-small (is-small-lmax l2 (is-contr (inclusion-subuniverse P X))) ,
      C5 X

    equiv-Σ-extension-analytic-unit-subuniverse :
      (X : UU l1) →
      Σ-extension-species-subuniverse
        ( P)
        ( Q)
        ( analytic-unit-species-subuniverse)
        ( X) ≃
      analytic-unit-species-types X
    pr1 (equiv-Σ-extension-analytic-unit-subuniverse X) =
      ( λ u →
        map-inv-equiv-is-small
          ( is-small-lmax l2 (is-contr X))
          (pr2 u))
    pr2 (equiv-Σ-extension-analytic-unit-subuniverse X) =
       is-equiv-has-inverse
         ( λ u →
           ( tr
             ( is-in-subuniverse P)
             ( eq-equiv
               ( raise-unit l1)
               ( X)
               ( ( inv-equiv
                   ( terminal-map ,
                     is-equiv-terminal-map-is-contr u )) ∘e
                 ( inv-equiv (compute-raise-unit l1))))
             ( C4))  , map-equiv-is-small (is-small-lmax l2 (is-contr X)) u)
         ( refl-htpy)
         ( λ x →
           ( eq-pair
             ( eq-is-contr
               ( is-proof-irrelevant-is-prop
                 ( is-prop-type-Prop (P X))
                 ( pr1 x)))
             ( eq-is-contr
               ( is-proof-irrelevant-is-prop
                ( is-prop-equiv
                  ( inv-equiv
                    ( compute-raise l2 (is-contr X)))
                    (is-property-is-contr))
                ( pr2 x)))))

    htpy-left-unit-law-comp-species-subuniverse :
      ( S : species-subuniverse P Q)
      ( X : type-subuniverse P) →
      inclusion-subuniverse
        ( Q)
        ( analytic-comp-species-subuniverse
          ( analytic-unit-species-subuniverse)
          ( S) X) ≃
      inclusion-subuniverse Q (S X)
    htpy-left-unit-law-comp-species-subuniverse S X =
      ( ( inv-equiv
          ( equiv-Σ-extension-species-subuniverse S X ) ) ∘e
<<<<<<< HEAD
      ( ( left-unit-law-comp-species-types
          ( Σ-extension-species-subuniverse P Q S)
          ( inclusion-subuniverse P X)) ∘e
      ( ( equiv-tot
          ( λ D →
            equiv-prod
              ( equiv-Σ-extension-analytic-unit-subuniverse
                ( indexing-type-Relaxed-Σ-Decomposition D))
              ( id-equiv))) ∘e
      ( ( equiv-analytic-comp-extension-species-subuniverse
          ( analytic-unit-species-subuniverse)
          ( S)
          ( inclusion-subuniverse P X)) ∘e
      ( ( equiv-Σ-extension-species-subuniverse
          ( analytic-comp-species-subuniverse
            ( analytic-unit-species-subuniverse)
            ( S))
          ( X)))))))
=======
        ( ( left-unit-law-comp-species-types
            ( Σ-extension-species-subuniverse P Q S)
            ( inclusion-subuniverse P X)) ∘e
          ( ( equiv-tot
              ( λ D →
                equiv-prod
                  ( equiv-Σ-extension-analytic-unit-subuniverse
                    ( indexing-type-Relaxed-Σ-Decomposition D))
                  ( id-equiv))) ∘e
            ( ( equiv-analytic-comp-extension-species-subuniverse
                ( analytic-unit-species-subuniverse)
                ( S)
                ( inclusion-subuniverse P X)) ∘e
              ( ( equiv-Σ-extension-species-subuniverse
                  ( analytic-comp-species-subuniverse
                    ( analytic-unit-species-subuniverse)
                    ( S))
                    ( X)))))))
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3

    left-unit-law-comp-species-subuniverse :
      ( S : species-subuniverse P Q) →
      analytic-comp-species-subuniverse analytic-unit-species-subuniverse S ＝ S
    left-unit-law-comp-species-subuniverse S =
      eq-equiv-fam-subuniverse
      ( Q)
      ( analytic-comp-species-subuniverse
        ( analytic-unit-species-subuniverse)
        ( S))
      ( S)
      ( htpy-left-unit-law-comp-species-subuniverse S)

    htpy-right-unit-law-comp-species-subuniverse :
      ( S : species-subuniverse P Q)
      ( X : type-subuniverse P) →
      inclusion-subuniverse
        ( Q)
        ( analytic-comp-species-subuniverse
          ( S)
          ( analytic-unit-species-subuniverse) X) ≃
      inclusion-subuniverse Q (S X)
    htpy-right-unit-law-comp-species-subuniverse S X =
      ( ( inv-equiv (equiv-Σ-extension-species-subuniverse S X) ) ∘e
<<<<<<< HEAD
      ( ( right-unit-law-comp-species-types
          ( Σ-extension-species-subuniverse P Q S)
          ( inclusion-subuniverse P X)) ∘e
      ( ( equiv-tot
          ( λ D →
            equiv-prod
              ( id-equiv)
              ( equiv-Π
                ( _)
                ( id-equiv)
                ( λ x →
                  equiv-Σ-extension-analytic-unit-subuniverse
                    ( cotype-Relaxed-Σ-Decomposition D x))))) ∘e
      ( ( equiv-analytic-comp-extension-species-subuniverse
            ( S)
            ( analytic-unit-species-subuniverse)
            ( inclusion-subuniverse P X)) ∘e
      ( ( equiv-Σ-extension-species-subuniverse
          ( analytic-comp-species-subuniverse
              S
              analytic-unit-species-subuniverse)
          X))))))
=======
        ( ( right-unit-law-comp-species-types
            ( Σ-extension-species-subuniverse P Q S)
            ( inclusion-subuniverse P X)) ∘e
          ( ( equiv-tot
              ( λ D →
                equiv-prod
                  ( id-equiv)
                  ( equiv-Π
                    ( _)
                    ( id-equiv)
                    ( λ x →
                      equiv-Σ-extension-analytic-unit-subuniverse
                        ( cotype-Relaxed-Σ-Decomposition D x))))) ∘e
            ( ( equiv-analytic-comp-extension-species-subuniverse
                  ( S)
                  ( analytic-unit-species-subuniverse)
                  ( inclusion-subuniverse P X)) ∘e
              ( ( equiv-Σ-extension-species-subuniverse
                  ( analytic-comp-species-subuniverse
                      S
                      analytic-unit-species-subuniverse)
                  ( X)))))))
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3

    right-unit-law-comp-species-subuniverse :
      ( S : species-subuniverse P Q) →
      analytic-comp-species-subuniverse S analytic-unit-species-subuniverse ＝ S
    right-unit-law-comp-species-subuniverse S =
      eq-equiv-fam-subuniverse
      ( Q)
      ( analytic-comp-species-subuniverse
        ( S)
        ( analytic-unit-species-subuniverse))
      ( S)
      ( htpy-right-unit-law-comp-species-subuniverse S)
```

<<<<<<< HEAD
### Associativity of composition of species-inhabited-types

```agda
  htpy-assoc-comp-species-inhabited-types :
=======
### Associativity of composition of species of types in subuniverse

```agda
  htpy-assoc-comp-species-subuniverse :
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
    (S : species-subuniverse P Q)
    (T : species-subuniverse P Q)
    (U : species-subuniverse P Q)
    (X : type-subuniverse P)→
    inclusion-subuniverse
      ( Q)
      ( analytic-comp-species-subuniverse
        ( S)
        ( analytic-comp-species-subuniverse T  U)
        ( X)) ≃
    inclusion-subuniverse
      ( Q)
      ( analytic-comp-species-subuniverse
        ( analytic-comp-species-subuniverse S T)
        ( U)
        ( X))
<<<<<<< HEAD
  htpy-assoc-comp-species-inhabited-types S T U X =
=======
  htpy-assoc-comp-species-subuniverse S T U X =
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
    ( ( inv-equiv
        ( equiv-Σ-extension-species-subuniverse
          ( analytic-comp-species-subuniverse
            ( analytic-comp-species-subuniverse S T) U)
          ( X))) ∘e
<<<<<<< HEAD
    ( ( inv-equiv
        ( equiv-analytic-comp-extension-species-subuniverse
          ( analytic-comp-species-subuniverse S T)
          ( U)
          ( inclusion-subuniverse P X))) ∘e
    ( ( equiv-tot
        λ D →
          equiv-prod
           ( inv-equiv
             ( equiv-analytic-comp-extension-species-subuniverse
               ( S)
               ( T)
               ( indexing-type-Relaxed-Σ-Decomposition D)))
           ( id-equiv) ) ∘e
    ( ( equiv-assoc-comp-species-types
        ( Σ-extension-species-subuniverse P Q S)
        ( Σ-extension-species-subuniverse P Q T)
        ( Σ-extension-species-subuniverse P Q U)
        ( inclusion-subuniverse P X)) ∘e
    ( ( equiv-tot
        ( λ D →
          equiv-prod
            ( id-equiv)
            ( equiv-Π
              ( λ y →
                ( analytic-comp-species-types
                  ( Σ-extension-species-subuniverse P Q T)
                  ( Σ-extension-species-subuniverse P Q U)
                  ( cotype-Relaxed-Σ-Decomposition D y)))
              ( id-equiv)
              ( λ y →
                ( equiv-analytic-comp-extension-species-subuniverse
                  ( T)
                  ( U)
                  ( cotype-Relaxed-Σ-Decomposition D y)))))) ∘e
      ( ( equiv-analytic-comp-extension-species-subuniverse
        ( S)
        ( analytic-comp-species-subuniverse T U)
        ( inclusion-subuniverse P X) ) ∘e
    ( ( equiv-Σ-extension-species-subuniverse
        ( analytic-comp-species-subuniverse
          ( S)
          ( analytic-comp-species-subuniverse T U))
        ( X)))))))))

  assoc-comp-species-inhabited-types :
=======
      ( ( inv-equiv
          ( equiv-analytic-comp-extension-species-subuniverse
            ( analytic-comp-species-subuniverse S T)
            ( U)
            ( inclusion-subuniverse P X))) ∘e
        ( ( equiv-tot
            λ D →
              equiv-prod
               ( inv-equiv
                 ( equiv-analytic-comp-extension-species-subuniverse
                   ( S)
                   ( T)
                   ( indexing-type-Relaxed-Σ-Decomposition D)))
               ( id-equiv) ) ∘e
          ( ( equiv-assoc-comp-species-types
              ( Σ-extension-species-subuniverse P Q S)
              ( Σ-extension-species-subuniverse P Q T)
              ( Σ-extension-species-subuniverse P Q U)
              ( inclusion-subuniverse P X)) ∘e
            ( ( equiv-tot
                ( λ D →
                  equiv-prod
                    ( id-equiv)
                    ( equiv-Π
                      ( λ y →
                        ( analytic-comp-species-types
                          ( Σ-extension-species-subuniverse P Q T)
                          ( Σ-extension-species-subuniverse P Q U)
                          ( cotype-Relaxed-Σ-Decomposition D y)))
                      ( id-equiv)
                      ( λ y →
                        ( equiv-analytic-comp-extension-species-subuniverse
                          ( T)
                          ( U)
                          ( cotype-Relaxed-Σ-Decomposition D y)))))) ∘e
              ( ( equiv-analytic-comp-extension-species-subuniverse
                  ( S)
                  ( analytic-comp-species-subuniverse T U)
                  ( inclusion-subuniverse P X) ) ∘e
                ( ( equiv-Σ-extension-species-subuniverse
                    ( analytic-comp-species-subuniverse
                      ( S)
                      ( analytic-comp-species-subuniverse T U))
                    ( X)))))))))

  assoc-comp-species-subuniverse :
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
    (S : species-subuniverse P Q)
    (T : species-subuniverse P Q)
    (U : species-subuniverse P Q)→
    analytic-comp-species-subuniverse
      ( S)
      ( analytic-comp-species-subuniverse T  U) ＝
    analytic-comp-species-subuniverse
      ( analytic-comp-species-subuniverse S T)
      ( U)
<<<<<<< HEAD
  assoc-comp-species-inhabited-types S T U =
=======
  assoc-comp-species-subuniverse S T U =
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
    eq-equiv-fam-subuniverse
      ( Q)
      ( analytic-comp-species-subuniverse
        ( S)
        ( analytic-comp-species-subuniverse T U))
      ( analytic-comp-species-subuniverse
        ( analytic-comp-species-subuniverse S T)
        ( U))
<<<<<<< HEAD
      ( htpy-assoc-comp-species-inhabited-types S T U)
```

## Examples

### Species of finite inhabited types

```agda
equiv-Σ-Decomposition-Inhabited-Type-𝔽-Σ-Decomposition-𝔽 :
  {l1 l2 : Level} (X : Inhabited-Type-𝔽 l1) →
  Σ-Decomposition-𝔽 l2 l2 (type-Inhabited-Type-𝔽 X) ≃
  Σ-Decomposition-subuniverse is-finite-and-inhabited-Prop ((type-Inhabited-Type-𝔽 X))
equiv-Σ-Decomposition-Inhabited-Type-𝔽-Σ-Decomposition-𝔽 X =
  ( ( inv-equiv
      ( equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse
        is-finite-and-inhabited-Prop)) ∘e
  ( ( equiv-tot
      ( λ D →
        equiv-prod
          ( equiv-add-redundant-prop
            ( is-property-is-inhabited _)
            ( λ _ →
              map-Inhabited-Type
                ( pr1 ∘ map-matching-correspondence-Relaxed-Σ-Decomposition D)
                ( is-inhabited-type-Inhabited-Type-𝔽 X)))
          ( id-equiv))) ∘e
  ( ( equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-𝔽))))

is-finite-Σ-Decomposition-subuniverse-Inhabited-Type-𝔽 :
  {l : Level} (X : Inhabited-Type-𝔽 l) →
  is-finite
    ( Σ-Decomposition-subuniverse
      ( is-finite-and-inhabited-Prop {l})
      ( type-Inhabited-Type-𝔽 X))
is-finite-Σ-Decomposition-subuniverse-Inhabited-Type-𝔽 X =
  is-finite-equiv
    ( equiv-Σ-Decomposition-Inhabited-Type-𝔽-Σ-Decomposition-𝔽 X)
    ( is-finite-Σ-Decomposition-𝔽 (finite-type-Inhabited-Type-𝔽 X))

finite-Σ-Decomposition-subuniverse-Inhabited-Type-𝔽 :
  {l : Level} (X :  Inhabited-Type-𝔽 l) → 𝔽 (lsuc l)
pr1 (finite-Σ-Decomposition-subuniverse-Inhabited-Type-𝔽 {l} X) =
  Σ-Decomposition-subuniverse
    ( is-finite-and-inhabited-Prop {l})
    ( type-Inhabited-Type-𝔽 X)
pr2 (finite-Σ-Decomposition-subuniverse-Inhabited-Type-𝔽 X) =
  is-finite-Σ-Decomposition-subuniverse-Inhabited-Type-𝔽 X

module _
  {l1 l2 : Level}
  where

  finite-analytic-comp-species-subuniverse :
    ( S T : species-Inhabited-Type-𝔽 l1 (l1 ⊔ l2) ) (X :  Inhabited-Type-𝔽 l1) →
    𝔽 (lsuc l1 ⊔ l2)
  finite-analytic-comp-species-subuniverse S T X =
    Σ-𝔽 ( finite-Σ-Decomposition-subuniverse-Inhabited-Type-𝔽 X)
        ( λ D →
           prod-𝔽
             ( S
               ( subuniverse-indexing-type-Σ-Decomposition-subuniverse
                   is-finite-and-inhabited-Prop
                   D))
             (( Π-𝔽
               ( finite-type-Inhabited-Type-𝔽
                 ( map-inv-compute-Inhabited-Type-𝔽'
                    ( subuniverse-indexing-type-Σ-Decomposition-subuniverse
                     is-finite-and-inhabited-Prop
                     D)))
               ( λ x →
                 T
                 ( subuniverse-cotype-Σ-Decomposition-subuniverse
                     is-finite-and-inhabited-Prop
                     D
                     x)))))

  private
    C1 :
      ( S T : species-Inhabited-Type-𝔽 l1 (l1 ⊔ l2) ) →
      ( X :  type-subuniverse is-finite-and-inhabited-Prop) →
      is-small
        (l1 ⊔ l2)
        ( analytic-comp-species-subuniverse'
          l2
          is-finite-and-inhabited-Prop
          is-finite-Prop
          S T X)
    C1 S T X =
      is-small-is-finite
        (l1 ⊔ l2)
        ( finite-analytic-comp-species-subuniverse S T
          (map-inv-compute-Inhabited-Type-𝔽' X) )

    C2 :
      ( S T : species-Inhabited-Type-𝔽 l1 (l1 ⊔ l2) ) →
      (X : type-subuniverse is-finite-and-inhabited-Prop) →
      is-finite (type-is-small (C1 S T X))
    C2 S T X =
      is-finite-equiv
        ( equiv-is-small (C1 S T X))
        ( is-finite-type-𝔽
          ( finite-analytic-comp-species-subuniverse
            ( S)
            ( T)
            ( map-inv-compute-Inhabited-Type-𝔽' X)))

    C3 :
      ( ( X : type-subuniverse {l1} is-finite-and-inhabited-Prop) →
        ( Y : ( inclusion-subuniverse is-finite-and-inhabited-Prop X) →
               type-subuniverse {l1} is-finite-and-inhabited-Prop) →
        is-in-subuniverse is-finite-and-inhabited-Prop
          ( Σ ( inclusion-subuniverse is-finite-and-inhabited-Prop X)
              ( λ x → inclusion-subuniverse is-finite-and-inhabited-Prop (Y x))))
    C3 X Y =
      is-finite-Σ
        ( is-finite-Inhabited-Type-𝔽 (map-inv-compute-Inhabited-Type-𝔽' X))
        ( λ x →
          is-finite-Inhabited-Type-𝔽 (map-inv-compute-Inhabited-Type-𝔽' (Y x))) ,
      is-inhabited-Σ
        ( is-inhabited-type-Inhabited-Type-𝔽
          ( map-inv-compute-Inhabited-Type-𝔽' X))
        ( λ x → is-inhabited-type-Inhabited-Type-𝔽
          ( map-inv-compute-Inhabited-Type-𝔽' (Y x)))

    C4 : is-finite-and-inhabited (raise-unit l1)
    C4 =
      is-finite-is-contr is-contr-raise-unit ,
      is-inhabited-is-contr is-contr-raise-unit

    C5 :
      ( X : type-subuniverse {l1} is-finite-and-inhabited-Prop) →
      ( is-finite
          ( type-is-small
            ( is-small-lmax
              ( l2)
              ( is-contr
                (inclusion-subuniverse is-finite-and-inhabited-Prop X)))))
    C5 X =
      is-finite-is-decidable-Prop
        ( _ ,
          is-prop-equiv
            ( inv-equiv
              ( equiv-is-small
                ( is-small-lmax l2
                  ( is-contr
                    ( type-Inhabited-Type-𝔽
                      ( map-inv-compute-Inhabited-Type-𝔽' X))))))
                ( is-property-is-contr))
        ( is-decidable-equiv
          ( inv-equiv
            ( equiv-is-small
              ( is-small-lmax
                ( l2)
                ( is-contr
                  ( type-Inhabited-Type-𝔽
                    ( map-inv-compute-Inhabited-Type-𝔽' X))))))
          ( is-decidable-is-contr-is-finite
            ( is-finite-Inhabited-Type-𝔽 (map-inv-compute-Inhabited-Type-𝔽' X))))

  analytic-comp-species-Inhabited-Type-𝔽 :
    species-Inhabited-Type-𝔽 l1 (l1 ⊔ l2) →
    species-Inhabited-Type-𝔽 l1 (l1 ⊔ l2)→
    species-Inhabited-Type-𝔽 l1 (l1 ⊔ l2)
  analytic-comp-species-Inhabited-Type-𝔽 =
    analytic-comp-species-subuniverse
      l2
      is-finite-and-inhabited-Prop
      is-finite-Prop
      C1 C2 C3

  analytic-unit-species-Inhabited-Type-𝔽 :
    species-Inhabited-Type-𝔽 l1 (l1 ⊔ l2)
  analytic-unit-species-Inhabited-Type-𝔽 =
    analytic-unit-species-subuniverse
      l2
      is-finite-and-inhabited-Prop
      is-finite-Prop
      C1 C2 C3 C4 C5

  left-unit-law-comp-species-Inhabited-Type-𝔽 :
    ( S : species-Inhabited-Type-𝔽 l1 (l1 ⊔ l2)) →
    analytic-comp-species-Inhabited-Type-𝔽
      analytic-unit-species-Inhabited-Type-𝔽
      S ＝
    S
  left-unit-law-comp-species-Inhabited-Type-𝔽 =
    left-unit-law-comp-species-subuniverse
      l2
      is-finite-and-inhabited-Prop
      is-finite-Prop
      C1 C2 C3 C4 C5

  right-unit-law-comp-species-Inhabited-Type-𝔽 :
    ( S : species-Inhabited-Type-𝔽 l1 (l1 ⊔ l2)) →
    analytic-comp-species-Inhabited-Type-𝔽
      S
      analytic-unit-species-Inhabited-Type-𝔽 ＝
    S
  right-unit-law-comp-species-Inhabited-Type-𝔽 =
    right-unit-law-comp-species-subuniverse
      l2
      is-finite-and-inhabited-Prop
      is-finite-Prop
      C1 C2 C3 C4 C5
```

### Species of inhabited types

```agda

=======
      ( htpy-assoc-comp-species-subuniverse S T U)
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
```
