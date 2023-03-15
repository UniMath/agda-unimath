# Composition of species of subuniverse

```agda
module univalent-combinatorics.composition-species-of-subuniverse where

open import foundation.cartesian-product-types
open import foundation.contractible-types
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
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels
open import univalent-combinatorics.large-composition-species-of-types
open import univalent-combinatorics.species-of-subuniverses
open import univalent-combinatorics.species-of-types
```

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
    Σ ( Σ-Decomposition-subuniverse P (inclusion-subuniverse P X))
      ( λ D →
        ( inclusion-subuniverse
          ( Q)
          ( S (subuniverse-indexing-type-Σ-Decomposition-subuniverse P D))) ×
        ( (x : indexing-type-Σ-Decomposition-subuniverse P D ) →
          inclusion-subuniverse
          ( Q)
          ( T (subuniverse-cotype-Σ-Decomposition-subuniverse P D x))))

module _
  {l1 : Level} (l2 : Level)
  (P : subuniverse l1 l1 )
  (Q : subuniverse (l1 ⊔ l2) (l1 ⊔ l2))
  (C1 :
    ( S T : species-subuniverse P Q ) → (X : type-subuniverse P) →
    is-small (l1 ⊔ l2) (analytic-comp-species-subuniverse' l2 P Q S T X))
  (C2 :
    ( S T : species-subuniverse P Q ) → (X : type-subuniverse P) →
    type-Prop (Q (type-is-small (C1 S T X))))
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
          ( ( equiv-tot (λ _ → inv-equiv (left-distributive-prod-Σ)))))))) ∘e
    ( ( assoc-Σ
        ( Relaxed-Σ-Decomposition l1 l1 X)
        ( λ D → is-in-subuniverse P (indexing-type-Relaxed-Σ-Decomposition D))
        ( _)) ∘e
    ( ( assoc-Σ
        ( Σ ( Relaxed-Σ-Decomposition l1 l1 X)
            ( λ D →
              is-in-subuniverse P (indexing-type-Relaxed-Σ-Decomposition D)))
        ( λ z →
          ( x : indexing-type-Relaxed-Σ-Decomposition (pr1 z)) →
          is-in-subuniverse P (cotype-Relaxed-Σ-Decomposition (pr1 z) x))
        ( _)) ∘e
    ( ( equiv-Σ-equiv-base
        ( _)
        ( equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse P ∘e
          ( inv-equiv
            ( equiv-add-redondent-prop
              ( is-prop-type-Prop (P X))
              ( λ D →
                ( tr
                  ( type-Prop ∘ P)
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
        ( type-Prop (P X))
        ( λ a → Σ-Decomposition-subuniverse P X)
        ( _)) ∘e
    ( ( equiv-tot (λ p → inv-equiv (equiv-is-small (C1 S T (X , p)))))))))))
```

### Unit laws for analytic composition of species-subuniverse

```agda
  module _
    (C4 : type-Prop (P (raise-unit l1)))
    (C5 :
      ( X : type-subuniverse P) →
      ( type-Prop
        ( Q
          ( type-is-small
            ( is-small-lmax l2 ( is-contr (inclusion-subuniverse P X)))))))
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
             ( type-Prop ∘ P)
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

    left-unit-law-comp-species-subuniverse :
      ( S : species-subuniverse P Q)
      ( X : type-subuniverse P) →
      inclusion-subuniverse
        ( Q)
        ( analytic-comp-species-subuniverse
          ( analytic-unit-species-subuniverse)
          ( S) X) ≃
      inclusion-subuniverse Q (S X)
    left-unit-law-comp-species-subuniverse S X =
      ( ( inv-equiv
          ( equiv-Σ-extension-species-subuniverse S X ) ) ∘e
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

    right-unit-law-comp-species-subuniverse :
      ( S : species-subuniverse P Q)
      ( X : type-subuniverse P) →
      inclusion-subuniverse
        ( Q)
        ( analytic-comp-species-subuniverse
          ( S)
          ( analytic-unit-species-subuniverse) X) ≃
      inclusion-subuniverse Q (S X)
    right-unit-law-comp-species-subuniverse S X =
      ( ( inv-equiv (equiv-Σ-extension-species-subuniverse S X) ) ∘e
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

```

### Associativity of composition of species-inhabited-types

```agda
  assoc-comp-species-inhabited-types' :
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
  assoc-comp-species-inhabited-types' S T U X =
    ( ( inv-equiv
        ( equiv-Σ-extension-species-subuniverse
          ( analytic-comp-species-subuniverse
            ( analytic-comp-species-subuniverse S T) U)
          ( X))) ∘e
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
    (S : species-subuniverse P Q)
    (T : species-subuniverse P Q)
    (U : species-subuniverse P Q)→
    analytic-comp-species-subuniverse
      ( S)
      ( analytic-comp-species-subuniverse T  U) ＝
    analytic-comp-species-subuniverse
      ( analytic-comp-species-subuniverse S T)
      ( U)
  assoc-comp-species-inhabited-types S T U =
    eq-equiv-fam-subuniverse
      ( Q)
      ( analytic-comp-species-subuniverse
        ( S)
        ( analytic-comp-species-subuniverse T U))
      ( analytic-comp-species-subuniverse
        ( analytic-comp-species-subuniverse S T)
        ( U))
      ( assoc-comp-species-inhabited-types' S T U)
```

## Examples

### Species of finite inhabited types

```agda

```

### Species of inhabited types

```agda

```
