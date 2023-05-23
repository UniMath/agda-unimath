# Products of Dirichlet series of species of types in subuniverses

```agda
module species.products-dirichlet-series-species-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.functions
open import foundation.subuniverses
open import foundation.universe-levels
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types

open import species.dirichlet-series-species-of-types-in-subuniverses
open import species.products-dirichlet-series-species-of-types
open import species.species-of-types-in-subuniverses
open import species.dirichlet-products-species-of-types-in-subuniverses
```

</details>

## Idea

The product of two Dirichlet series is the pointwise product.

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse id)
  (C1 : is-closed-under-products-subuniverse P)
  (H : species-subuniverse-domain l5 P)
  (C2 : preserves-product-species-subuniverse-domain P C1 H)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (X : UU l6)
  where

  product-dirichlet-series-species-subuniverse : UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  product-dirichlet-series-species-subuniverse =
    dirichlet-series-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q l3)
      ( C1)
      ( H)
      ( C2)
      ( S)
      ( X) ×
    dirichlet-series-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q l4)
      ( C1)
      ( H)
      ( C2)
      ( T)
      ( X)
```

## Properties

### The Dirichlet series associated to the Dirichlet product of `S` and `T` is equal to the product of theirs Dirichlet series

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse id)
  (C1 : is-closed-under-products-subuniverse P)
  (H : species-subuniverse-domain l5 P)
  (C2 : preserves-product-species-subuniverse-domain P C1 H)
  (C3 : is-closed-under-dirichlet-product-species-subuniverse P Q)
  (C4 : is-closed-under-coproducts-subuniverse P)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (X : UU l5)
  where

  private
    reassociate :
      dirichlet-series-species-subuniverse
        ( P)
        ( Q)
        ( C1)
        ( H)
        ( C2)
        ( dirichlet-product-species-subuniverse S T) X ≃
      Σ ( UU l1)
        ( λ A →
          Σ ( UU l1)
            ( λ B →
              Σ ( Σ ( UU l1) (λ F → F ≃ (A × B)))
                ( λ F → ((S A) × (T B)) × (X → H (pr1 F)))))
    pr1 reassociate (F , ((A , B , e) , x) , y) = (A , B , (F , e) , x , y)
    pr2 reassociate =
      is-equiv-has-inverse
        ( λ (A , B , (F , e) , x , y) → (F , ((A , B , e) , x) , y))
        ( refl-htpy)
        ( refl-htpy)

--     reassociate' :
--       Σ ( UU l1)
--         ( λ A → Σ (UU l1) (λ B → (S A × T B) × ((X → H A) × (X → H B)))) ≃
--       product-dirichlet-series-species-types H C1 S T X
--     pr1 reassociate' (A , B , (s , t) , (fs , ft)) =
--       ((A , (s , fs)) , (B , (t , ft)))
--     pr2 reassociate' =
--       is-equiv-has-inverse
--         ( λ ((A , (s , fs)) , (B , (t , ft))) →
--           (A , B , (s , t) , (fs , ft)))
--         ( refl-htpy)
--         ( refl-htpy)

--   equiv-dirichlet-series-dirichlet-product-species-types :
--     dirichlet-series-species-types
--       ( H)
--       ( C1)
--       ( dirichlet-product-species-types S T)
--       ( X) ≃
--     product-dirichlet-series-species-types H C1 S T X
--   equiv-dirichlet-series-dirichlet-product-species-types =
--      ( reassociate') ∘e
--      ( ( equiv-tot
--          ( λ A →
--            equiv-tot
--              ( λ B →
--                ( equiv-prod
--                  ( id-equiv)
--                  ( universal-property-product ∘e
--                    equiv-postcomp X (C1 A B))) ∘e
--                ( left-unit-law-Σ-is-contr
--                  ( is-contr-total-equiv' (A × B))
--                  ( A × B , id-equiv))))) ∘e
--        ( reassociate))
-- ```
