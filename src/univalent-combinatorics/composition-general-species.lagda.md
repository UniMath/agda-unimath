#  Composition of general species

```agda
module univalent-combinatorics.composition-general-species where

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.univalence
open import foundation.universe-levels
open import foundation.universal-property-dependent-pair-types
open import foundation.sigma-decompositions
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
```

## Idea

A general species `S : UU l1 → UU l2` can be thought of as the analytic endofunctor

```md
  X ↦ Σ (A : UU l1) (S A) × (A → X)
```

Using the formula for composition of analytic endofunctors, we obtain a way to compose species.

## Definition

### Analytic composition of species

```agda
analytic-comp-general-species :
  {l1 l2 l3 : Level} → general-species l1 l2 → general-species l1 l3 →
  general-species l1 (lsuc l1 ⊔ l2 ⊔ l3)
analytic-comp-general-species {l1} {l2} {l3} S T X =
  Σ ( Σ-Decomposition l1 l1 X)
    ( λ D →
      ( S (indexing-type-Σ-Decomposition D) ×
      ( (y : indexing-type-Σ-Decomposition D) →
      T (cotype-Σ-Decomposition D y ))))
```

 ### The analytic unit for composition of species

 ```agda
analytic-unit-general-species : {l1 : Level} → general-species l1 l1
analytic-unit-general-species X = is-contr X
```

## Properties

### Unit laws for analytic composition of species

```agda
{-
left-unit-law-comp-species :
  {l1 l2 : Level} (F : species l1 l2) →
  equiv-species (analytic-comp-species analytic-unit-species F) F
left-unit-law-comp-species F X =
  {!!}
-}
```

### Associativity of composition of species

```agda
module _
  {l1 l2 l3 l4 : Level} 
  (S : general-species l1 l2) (T : general-species l1 l3)
  (U : general-species l1 l4)
  where

  equiv-assoc-comp-general-species :
    (A : UU l1) →
    ( analytic-comp-general-species S (analytic-comp-general-species T  U) A) ≃
    ( analytic-comp-general-species (analytic-comp-general-species S T) U A)
  equiv-assoc-comp-general-species A =
    ( ( equiv-Σ
        ( _)
        ( id-equiv)
        ( λ D1 →
          ( ( inv-equiv right-distributive-prod-Σ)  ∘e
          ( ( equiv-Σ
              ( _)
              ( id-equiv)
              ( λ D2 →
                ( inv-assoc-Σ
                  ( S (indexing-type-Σ-Decomposition D2))
                  ( λ _ →
                    ( x : indexing-type-Σ-Decomposition D2) →
                    T ( cotype-Σ-Decomposition D2 x))
                  _))) ∘e
          ( ( equiv-Σ
            ( _)
            ( id-equiv)
            ( λ D2 →
              ( equiv-prod
                ( id-equiv)
                ( ( equiv-prod
                    ( id-equiv)
                    ( ( inv-equiv
                        ( equiv-precomp-Π
                          ( inv-equiv
                            ( matching-correspondence-Σ-Decomposition D2) )
                        ( λ x → U ( cotype-Σ-Decomposition D1 x) ))) ∘e
                      ( inv-equiv equiv-ev-pair))) ∘e
                  ( distributive-Π-Σ)))))))))) ∘e
    ( ( assoc-Σ
        ( Σ-Decomposition l1 l1 A)
        ( λ D → Σ-Decomposition l1 l1
          ( indexing-type-Σ-Decomposition D))
        ( _)) ∘e
    ( ( inv-equiv
        ( equiv-Σ-equiv-base
          ( _ )
          ( equiv-displayed-fibered-Σ-Decomposition))) ∘e
    ( ( inv-assoc-Σ
        ( Σ-Decomposition l1 l1 A)
        ( λ D →
          ( x : indexing-type-Σ-Decomposition D) →
            Σ-Decomposition l1 l1
              ( cotype-Σ-Decomposition D x))
        ( _)) ∘e
    ( ( equiv-Σ
        ( _)
        ( id-equiv)
        ( λ D → left-distributive-prod-Σ)) ∘e
    ( ( equiv-Σ
        ( _)
        ( id-equiv)
        ( λ D → equiv-prod id-equiv distributive-Π-Σ))))))))

  htpy-assoc-comp-general-species :
    ( analytic-comp-general-species S (analytic-comp-general-species T  U)) ~
    ( analytic-comp-general-species (analytic-comp-general-species S T) U)
  htpy-assoc-comp-general-species A =
    eq-equiv
      ( analytic-comp-general-species S (analytic-comp-general-species T U)
        A)
      ( analytic-comp-general-species (analytic-comp-general-species S T) U
        A)
      ( equiv-assoc-comp-general-species A)

  assoc-comp-general-species :
    ( analytic-comp-general-species S (analytic-comp-general-species T  U)) ＝
    ( analytic-comp-general-species (analytic-comp-general-species S T) U)
  assoc-comp-general-species = eq-htpy htpy-assoc-comp-general-species

```
