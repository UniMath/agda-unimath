#  Composition of species

```agda
module univalent-combinatorics.composition-species-of-finite-types where

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
open import foundation.propositions
open import foundation.propositional-truncations
open import foundation.univalence
open import foundation.universe-levels
open import foundation.universal-property-dependent-pair-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.composition-species-of-types
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-sum-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.species-of-finite-types
open import univalent-combinatorics.partitions
open import univalent-combinatorics.sigma-decompositions
```

## Idea

A species `S : 𝔽 → 𝔽 l` can be thought of as the analytic endofunctor

```md
  X ↦ Σ (A : 𝔽) (S A) × (A → X)
```

Using the formula for composition of analytic endofunctors, we obtain a way to compose species.

## Definition

### Analytic composition of species

```agda
analytic-comp-species-finite-types :
  {l1 l2 l3 : Level} → species-finite-types l1 l2 → species-finite-types l1 l3 →
  species-finite-types l1 (lsuc l1 ⊔ l2 ⊔ l3)
analytic-comp-species-finite-types {l1} {l2} {l3} S T X =
  Σ-𝔽 ( Σ-Decomposition-𝔽 l1 l1 (type-𝔽 X))
    ( λ D →
      prod-𝔽
        ( S ( finite-indexing-type-Σ-Decomposition-𝔽 D)) 
        ( Π-𝔽
          ( finite-indexing-type-Σ-Decomposition-𝔽 D)
          ( λ y → T (finite-cotype-Σ-Decomposition-𝔽 D y ))))
```

 ### The analytic unit for composition of species-finite-type

 ```agda
analytic-unit-species-finite-types : {l1 : Level} → species-finite-types l1 l1
analytic-unit-species-finite-types X = is-contr (type-𝔽 X)
```

## Properties

### Equivalent form with species of types

```agda
module _
  {l1 l2 : Level} (S : species-finite-types l1 l2)
  where

  equiv-Σ-extension-species-finite-types :
    ( X : 𝔽 l1) →
    S X ≃ Σ-extension-species-finite-types S (type-𝔽 (X))
  equiv-Σ-extension-species-finite-types X =
    inv-left-unit-law-Σ-is-contr
      ( is-proof-irrelevant-is-prop
        ( is-prop-is-finite (type-𝔽 X))
        ( is-finite-type-𝔽 X))
      ( is-finite-type-𝔽 X)

-- module _
--   {l1 l2 l3 : Level} (S : species l1 l2) (T : species l1 l3)
--   where

--   equiv-analytic-comp-generalized-species :
--     (X : UU l1) →
--     Σ-generalized-species (analytic-comp-species S T) X ≃
--     analytic-comp-general-species
--       ( Σ-generalized-species {l1} {l2} S)
--       ( Σ-generalized-species {l1} {l3} T) X
--   equiv-analytic-comp-generalized-species X =
--       ( ( equiv-Σ
--           ( λ D →
--             Σ-generalized-species {l1} {l2} S (indexing-type-Σ-Decomposition D) ×
--             ( (y : indexing-type-Σ-Decomposition D) →
--               Σ-generalized-species {l1} {l3} T (cotype-Σ-Decomposition D y)))
--           ( id-equiv)
--           ( λ D →
--             ( equiv-prod id-equiv ( inv-equiv distributive-Π-Σ))∘e
--             ( ( inv-equiv right-distributive-prod-Σ ) ∘e
--             (equiv-Σ
--               ( _)
--               ( id-equiv)
--               ( λ _ → inv-equiv left-distributive-prod-Σ)))))∘e
--         ( ( assoc-Σ
--             ( Σ-Decomposition l1 l1 X)
--             ( λ D → is-finite (indexing-type-Σ-Decomposition D))
--             ( _)) ∘e
--         ( ( assoc-Σ
--             ( Σ ( Σ-Decomposition l1 l1 X)
--                 ( λ D → is-finite (indexing-type-Σ-Decomposition D )))
--             ( λ z →
--               ( x : indexing-type-Σ-Decomposition (pr1 z)) →
--               is-finite (cotype-Σ-Decomposition (pr1 z) x))
--             ( _)) ∘e
--         ( ( equiv-Σ-equiv-base
--               ( _)
--               ( ( inv-assoc-Σ
--                   ( Σ-Decomposition l1 l1 X )
--                   ( λ D → is-finite (indexing-type-Σ-Decomposition D))
--                   ( _)) ∘e
--               (  ( inv-equiv
--                   ( equiv-Σ-Decomposition-𝔽-is-finite-subtype) ∘e
--               ( inv-equiv
--                 ( ( λ D → (is-finite-base-type-Σ-Decomposition-𝔽 D , D)) ,
--                   is-equiv-has-inverse
--                     ( pr2)
--                     ( λ x →
--                       eq-pair
--                         ( center (is-prop-is-finite X _ _ ))
--                         ( refl))
--                     ( refl-htpy))))))) ∘e
--         inv-assoc-Σ (is-finite X) (λ _ → Σ-Decomposition-𝔽 l1 l1 X) _))))
-- ```

-- ### Unit laws for analytic composition of species

-- ```agda
-- {-
-- left-unit-law-comp-species :
--   {l1 l2 : Level} (F : species l1 l2) →
--   equiv-species (analytic-comp-species analytic-unit-species F) F
-- left-unit-law-comp-species F X =
--   {!!}
-- -}
-- ```

-- ### Associativity of composition of species

-- ```agda
-- assoc-comp-species :
--   {l1 l2 l3 l4 : Level} →
--   (S : species l1 l2) (T : species l1 l3)
--   (U : species l1 l4) →
--   ( analytic-comp-species S (analytic-comp-species T  U)) ＝
--   ( analytic-comp-species (analytic-comp-species S T) U)
-- assoc-comp-species {l1} {l2} {l3} {l4} S T U =
--   eq-equiv-fam
--     ( λ X →
--       ( ( inv-equiv
--           ( equiv-species-generalized-species
--             ( analytic-comp-species ( analytic-comp-species S T) U)
--             ( X))) ∘e
--       ( ( inv-equiv
--           ( equiv-analytic-comp-generalized-species
--              ( analytic-comp-species S T)
--              ( U)
--              ( type-𝔽 X)) ) ∘e
--       ( ( equiv-Σ
--           ( λ D →
--               Σ-generalized-species
--                 ( analytic-comp-species S T)
--                 ( indexing-type-Σ-Decomposition D) ×
--               ( (y : indexing-type-Σ-Decomposition D) →
--                 Σ-generalized-species U (cotype-Σ-Decomposition D y)))
--           ( id-equiv)
--           ( λ D →
--             ( equiv-prod
--               ( inv-equiv
--                 ( equiv-analytic-comp-generalized-species
--                   ( S)
--                   ( T)
--                   ( indexing-type-Σ-Decomposition D))))
--               ( id-equiv))) ∘e
--       ( ( equiv-assoc-comp-general-species
--           ( Σ-generalized-species {l1} {l2} S)
--           ( Σ-generalized-species {l1} {l3} T)
--           ( Σ-generalized-species {l1} {l4} U)
--           ( type-𝔽 X)) ∘e
--       ( ( equiv-Σ
--           (λ D →
--               Σ-generalized-species S (indexing-type-Σ-Decomposition D) ×
--               ( ( y : indexing-type-Σ-Decomposition D) →
--                 ( analytic-comp-general-species
--                   ( Σ-generalized-species T)
--                   ( Σ-generalized-species U)
--                   (cotype-Σ-Decomposition D y))))
--           ( id-equiv)
--           ( λ D →
--             equiv-prod
--               ( id-equiv)
--               ( equiv-Π
--                 ( λ y →
--                    ( analytic-comp-general-species
--                      ( Σ-generalized-species T)
--                      ( Σ-generalized-species U)
--                      (cotype-Σ-Decomposition D y)))
--                 ( id-equiv)
--                 ( λ y →
--                   ( equiv-analytic-comp-generalized-species
--                     ( T)
--                     ( U)
--                     ( cotype-Σ-Decomposition D y)))))) ∘e
--       ( ( equiv-analytic-comp-generalized-species
--           ( S)
--           ( analytic-comp-species T U)
--           ( type-𝔽 X)) ∘e
--       ( equiv-species-generalized-species
--         ( analytic-comp-species S (analytic-comp-species T U))
--         ( X)))))))))
--  ```
