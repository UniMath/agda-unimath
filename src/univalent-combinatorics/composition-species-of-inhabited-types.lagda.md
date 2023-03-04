#  Composition of species of inhabited types

```agda
module univalent-combinatorics.composition-species-of-inhabited-types where

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
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
open import foundation.univalence
open import foundation.universe-levels
open import foundation.universal-property-dependent-pair-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice

open import univalent-combinatorics.composition-species-of-types
open import univalent-combinatorics.dependent-sum-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.partitions
open import univalent-combinatorics.sigma-decompositions
open import univalent-combinatorics.species-of-inhabited-types
open import univalent-combinatorics.species-of-types
```

## Idea

A species `S : Inhabited-Type → UU l` can be thought of as the analytic endofunctor

```md
  X ↦ Σ (A : Inhabited-Type) (S A) × (A → X)
```

Using the formula for composition of analytic endofunctors, we obtain a way to compose species.

## Definition

### Analytic composition of species

```agda
analytic-comp-species-inhabited-types :
  {l1 l2 l3 : Level} →
  species-inhabited-types l1 l2 →
  species-inhabited-types l1 l3 →
  species-inhabited-types l1 (lsuc l1 ⊔ l2 ⊔ l3)
analytic-comp-species-inhabited-types {l1} {l2} {l3} S T X =
  Σ ( Σ-Decomposition l1 l1 (type-Inhabited-Type X))
    ( λ D →
      ( S ( inhabited-indexing-type-inhabited-Σ-Decomposition
            ( D)
            (is-inhabited-type-Inhabited-Type X))
        ×
        ( ( y : indexing-type-Σ-Decomposition D) →
          T (inhabited-cotype-Σ-Decomposition D y ))))
```

 ### The analytic unit for composition of species-inhabited-types

 ```agda
analytic-unit-species-inhabited-types :
  {l1 : Level} → species-inhabited-types l1 l1
analytic-unit-species-inhabited-types X = is-contr (type-Inhabited-Type X)
```

## Properties

### Equivalent form with species of types

```agda
module _
  {l1 l2 : Level} (S : species-inhabited-types l1 l2)
  where

  equiv-Σ-extension-species-inhabited-types :
    ( X : Inhabited-Type l1) →
    S X ≃ Σ-extension-species-inhabited-types S ( type-Inhabited-Type X)
  equiv-Σ-extension-species-inhabited-types X =
    inv-left-unit-law-Σ-is-contr
      ( is-proof-irrelevant-is-prop
        ( is-property-is-inhabited (type-Inhabited-Type X))
        ( is-inhabited-type-Inhabited-Type X))
      ( is-inhabited-type-Inhabited-Type X)

module _
  {l1 l2 l3 : Level} (S : species-inhabited-types l1 l2) (T : species-inhabited-types l1 l3)
  where

  equiv-analytic-comp-extension-species-inhabited-types :
    (X : UU l1) →
    Σ-extension-species-inhabited-types (analytic-comp-species-inhabited-types S T) X ≃
    analytic-comp-species-types
      ( Σ-extension-species-inhabited-types {l1} {l2} S)
      ( Σ-extension-species-inhabited-types {l1} {l3} T) X
  equiv-analytic-comp-extension-species-inhabited-types X =
      ( ( equiv-Σ
          ( λ D →
            Σ-extension-species-inhabited-types {l1} {l2} S (indexing-type-Σ-Decomposition D) ×
            ( (y : indexing-type-Σ-Decomposition D) →
              Σ-extension-species-inhabited-types {l1} {l3} T (cotype-Σ-Decomposition D y)))
          ( id-equiv)
          ( λ D →
            ( equiv-prod id-equiv ( inv-equiv distributive-Π-Σ))∘e
            ( ( inv-equiv right-distributive-prod-Σ ) ∘e
            (equiv-Σ
              ( _)
              ( id-equiv)
              ( λ _ → inv-equiv left-distributive-prod-Σ)))))∘e
        ( ( assoc-Σ
            ( Σ-Decomposition l1 l1 X)
            ( λ D → is-inhabited (indexing-type-Σ-Decomposition D))
            ( _)) ∘e
        ( ( assoc-Σ
            ( Σ ( Σ-Decomposition l1 l1 X)
                ( λ D → is-inhabited (indexing-type-Σ-Decomposition D )))
            ( λ z →
              ( x : indexing-type-Σ-Decomposition (pr1 z)) →
              is-inhabited (cotype-Σ-Decomposition (pr1 z) x))
            ( _)) ∘e
        ( ( equiv-Σ-equiv-base
            ( _)
            ( ( λ is-inhab-X--D →
                ( ( pr2 is-inhab-X--D ,
                    is-inhabited-indexing-type-inhabited-Σ-Decomposition
                      ( pr2 is-inhab-X--D)
                      ( pr1 is-inhab-X--D)) ,
                  ( is-inhabited-cotype-Σ-Decomposition (pr2 is-inhab-X--D)))) ,
              ( is-equiv-has-inverse
                ( λ x →
                  ( ( is-inhabited-base-is-inhabited-indexing-type-Σ-Decomposition
                      ( pr1 (pr1 x))
                      ( pr2 (pr1 x))) ,
                    ( pr1 (pr1 x))))
                ( λ x →
                  eq-pair-Σ
                    ( eq-pair-Σ
                      refl
                      ( center
                        ( is-property-is-inhabited
                          ( indexing-type-Σ-Decomposition (pr1 (pr1 x))) _ _)))
                    ( center
                      ( is-prop-Π
                        ( λ y → is-property-is-inhabited (cotype-Σ-Decomposition (pr1 (pr1 x)) y))
                        ( _)
                        ( _))))
                ( λ x →
                  eq-pair
                    ( center
                      ( is-property-is-inhabited X _ _))
                      refl))) ) ∘e
        ( ( inv-assoc-Σ
            ( is-inhabited X)
            ( λ _ → Σ-Decomposition l1 l1 X)
            ( _)))))))
```

### Unit laws for analytic composition of species-inhabited-types

```agda

left-unit-law-comp-species-inhabited-types :
  {l1 l2 : Level}
  (F : species-inhabited-types l1 l2) → (A : Inhabited-Type l1) →
  ( analytic-comp-species-inhabited-types
    ( analytic-unit-species-inhabited-types)
    ( F)) A ≃
  F A
left-unit-law-comp-species-inhabited-types F A =
  ( ( inv-equiv
      ( equiv-Σ-extension-species-inhabited-types
        ( F)
        ( A))) ∘e
  ( ( left-unit-law-comp-inhabited-species-types
      ( Σ-extension-species-inhabited-types F)
      ( type-Inhabited-Type A)
      ( is-inhabited-type-Inhabited-Type A)) ∘e
  ( ( equiv-Σ
      ( _)
      ( id-equiv)
      ( λ D →
        equiv-prod
          ( left-unit-law-Σ-is-contr
            ( is-proof-irrelevant-is-prop
              ( is-property-is-inhabited (indexing-type-Σ-Decomposition D))
              ( is-inhabited-indexing-type-inhabited-Σ-Decomposition
                ( D)
                ( is-inhabited-type-Inhabited-Type A)))
            ( is-inhabited-indexing-type-inhabited-Σ-Decomposition
              ( D)
              ( is-inhabited-type-Inhabited-Type A)))
          ( id-equiv))) ∘e
  ( ( equiv-analytic-comp-extension-species-inhabited-types
      ( analytic-unit-species-inhabited-types)
      ( F)
      (( type-Inhabited-Type A))) ∘e
  ( ( equiv-Σ-extension-species-inhabited-types
      ( analytic-comp-species-inhabited-types
        ( analytic-unit-species-inhabited-types)
        ( F))
      ( A)))))))

right-unit-law-comp-species-inhabited-types :
  {l1 l2 : Level}
  (F : species-inhabited-types l1 l2) → (A : Inhabited-Type l1) →
  ( analytic-comp-species-inhabited-types
    ( F)
    ( analytic-unit-species-inhabited-types)) A ≃
  F A
right-unit-law-comp-species-inhabited-types F A =
  ( ( inv-equiv
      ( equiv-Σ-extension-species-inhabited-types
        ( F)
        ( A))) ∘e
  ( ( right-unit-law-comp-species-types
      ( Σ-extension-species-inhabited-types F)
      ( type-Inhabited-Type A)) ∘e
  ( ( equiv-Σ
      ( _)
      ( id-equiv)
      ( λ D →
        equiv-prod
          ( id-equiv)
          ( equiv-Π
            ( _)
            ( id-equiv)
            ( λ x →
              ( left-unit-law-Σ-is-contr
                ( is-proof-irrelevant-is-prop
                  ( is-property-is-inhabited (cotype-Σ-Decomposition D x))
                  ( is-inhabited-cotype-Σ-Decomposition D x))
                ( is-inhabited-cotype-Σ-Decomposition D x)))))) ∘e
  ( ( equiv-analytic-comp-extension-species-inhabited-types
      ( F)
      ( analytic-unit-species-inhabited-types)
      (( type-Inhabited-Type A))) ∘e
  ( ( equiv-Σ-extension-species-inhabited-types
      ( analytic-comp-species-inhabited-types
        ( F)
        ( analytic-unit-species-inhabited-types))
      ( A)))))))


```

### Associativity of composition of species-inhabited-types

```agda
assoc-comp-species-inhabited-types :
  {l1 l2 l3 l4 : Level} →
  (S : species-inhabited-types l1 l2) (T : species-inhabited-types l1 l3)
  (U : species-inhabited-types l1 l4) →
  ( analytic-comp-species-inhabited-types S (analytic-comp-species-inhabited-types T  U)) ＝
  ( analytic-comp-species-inhabited-types (analytic-comp-species-inhabited-types S T) U)
assoc-comp-species-inhabited-types {l1} {l2} {l3} {l4} S T U =
  eq-equiv-fam
    ( λ X →
      ( ( inv-equiv
          ( equiv-Σ-extension-species-inhabited-types
            ( analytic-comp-species-inhabited-types ( analytic-comp-species-inhabited-types S T) U)
            ( X))) ∘e
      ( ( inv-equiv
          ( equiv-analytic-comp-extension-species-inhabited-types
             ( analytic-comp-species-inhabited-types S T)
             ( U)
             ( type-Inhabited-Type X)) ) ∘e
      ( ( equiv-Σ
          ( λ D →
              Σ-extension-species-inhabited-types
                ( analytic-comp-species-inhabited-types S T)
                ( indexing-type-Σ-Decomposition D) ×
              ( (y : indexing-type-Σ-Decomposition D) →
                Σ-extension-species-inhabited-types U (cotype-Σ-Decomposition D y)))
          ( id-equiv)
          ( λ D →
            ( equiv-prod
              ( inv-equiv
                ( equiv-analytic-comp-extension-species-inhabited-types
                  ( S)
                  ( T)
                  ( indexing-type-Σ-Decomposition D))))
              ( id-equiv))) ∘e
      ( ( equiv-assoc-comp-species-types
          ( Σ-extension-species-inhabited-types {l1} {l2} S)
          ( Σ-extension-species-inhabited-types {l1} {l3} T)
          ( Σ-extension-species-inhabited-types {l1} {l4} U)
          ( type-Inhabited-Type X)) ∘e
      ( ( equiv-Σ
          (λ D →
              Σ-extension-species-inhabited-types S (indexing-type-Σ-Decomposition D) ×
              ( ( y : indexing-type-Σ-Decomposition D) →
                ( analytic-comp-species-types
                  ( Σ-extension-species-inhabited-types T)
                  ( Σ-extension-species-inhabited-types U)
                  (cotype-Σ-Decomposition D y))))
          ( id-equiv)
          ( λ D →
            equiv-prod
              ( id-equiv)
              ( equiv-Π
                ( λ y →
                   ( analytic-comp-species-types
                     ( Σ-extension-species-inhabited-types T)
                     ( Σ-extension-species-inhabited-types U)
                     (cotype-Σ-Decomposition D y)))
                ( id-equiv)
                ( λ y →
                  ( equiv-analytic-comp-extension-species-inhabited-types
                    ( T)
                    ( U)
                    ( cotype-Σ-Decomposition D y)))))) ∘e
      ( ( equiv-analytic-comp-extension-species-inhabited-types
          ( S)
          ( analytic-comp-species-inhabited-types T U)
          ( type-Inhabited-Type X)) ∘e
      ( equiv-Σ-extension-species-inhabited-types
        ( analytic-comp-species-inhabited-types S (analytic-comp-species-inhabited-types T U))
        ( X)))))))))
 ```
