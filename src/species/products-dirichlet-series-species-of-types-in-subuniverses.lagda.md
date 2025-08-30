# Products of Dirichlet series of species of types in subuniverses

```agda
module species.products-dirichlet-series-species-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.global-subuniverses
open import foundation.homotopies
open import foundation.postcomposition-functions
open import foundation.subuniverses
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-cartesian-product-types
open import foundation.universe-levels

open import species.dirichlet-products-species-of-types-in-subuniverses
open import species.dirichlet-series-species-of-types-in-subuniverses
open import species.species-of-types-in-subuniverses
```

</details>

## Idea

The
{{#concept "product" Disambiguation="of Caucy series of species of types in subuniverses" Agda=product-dirichlet-series-species-subuniverse}}
of two
[Dirichlet series](species.dirichlet-series-species-of-types-in-subuniverses.md)
of
[species of types in subuniverses](species.species-of-types-in-subuniverses.md)
is just the pointwise [product](foundation.cartesian-product-types.md).

## Definition

```agda
module _
  {α : Level → Level} {l1 l2 l3 l4 l5 l6 : Level}
  (P : subuniverse l1 l2) (Q : global-subuniverse α)
  (C1 : is-closed-under-products-subuniverse P)
  (H : species-subuniverse-domain l5 P)
  (C2 : preserves-product-species-subuniverse-domain P C1 H)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (X : UU l6)
  where

  product-dirichlet-series-species-subuniverse :
    UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
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

### The Dirichlet series associated to the Dirichlet product of `S` and `T` is equal to the product of their Dirichlet series

```agda
module _
  {α : Level → Level} {l1 l2 l3 l4 l5 : Level}
  (P : subuniverse l1 l2) (Q : global-subuniverse α)
  (C1 : is-closed-under-products-subuniverse P)
  (H : species-subuniverse-domain l5 P)
  (C2 : preserves-product-species-subuniverse-domain P C1 H)
  (C3 : is-closed-under-dirichlet-product-species-subuniverse P Q)
  (C4 : is-closed-under-coproducts-subuniverse P)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (X : UU l5)
  where

  equiv-dirichlet-series-dirichlet-product-species-subuniverse :
    dirichlet-series-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
      ( C1)
      ( H)
      ( C2)
      ( dirichlet-product-species-subuniverse P Q C3 S T)
      ( X) ≃
    product-dirichlet-series-species-subuniverse P Q C1 H C2 S T X
  equiv-dirichlet-series-dirichlet-product-species-subuniverse =
    ( reassociate') ∘e
    ( equiv-tot
      ( λ A →
        equiv-tot
          ( λ B →
            ( equiv-product-right
              ( equiv-up-product ∘e equiv-postcomp X (C2 A B))) ∘e
            ( left-unit-law-Σ-is-contr
              ( is-torsorial-equiv-subuniverse'
                ( P)
                ( inclusion-subuniverse P A ×
                  inclusion-subuniverse P B ,
                  C1
                    ( is-in-subuniverse-inclusion-subuniverse P A)
                    ( is-in-subuniverse-inclusion-subuniverse P B)))
              ( ( inclusion-subuniverse P A × inclusion-subuniverse P B ,
                  C1
                    ( is-in-subuniverse-inclusion-subuniverse P A)
                    ( is-in-subuniverse-inclusion-subuniverse P B)) ,
                ( id-equiv)))))) ∘e
    ( reassociate)
    where
    reassociate :
      dirichlet-series-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
        ( C1)
        ( H)
        ( C2)
        ( dirichlet-product-species-subuniverse P Q C3 S T) X ≃
      Σ ( type-subuniverse P)
        ( λ A →
          Σ ( type-subuniverse P)
            ( λ B →
              Σ ( Σ ( type-subuniverse P)
                    ( λ F →
                      inclusion-subuniverse P F ≃
                      ( inclusion-subuniverse P A × inclusion-subuniverse P B)))
                ( λ F →
                  ( ( inclusion-subuniverse
                      ( subuniverse-global-subuniverse Q l3)
                      ( S A)) ×
                    ( inclusion-subuniverse
                      ( subuniverse-global-subuniverse Q l4)
                      ( T B))) × (X → H (pr1 F)))))
    pr1 reassociate (F , ((A , B , e) , x) , y) = (A , B , (F , e) , x , y)
    pr2 reassociate =
      is-equiv-is-invertible
        ( λ (A , B , (F , e) , x , y) → (F , ((A , B , e) , x) , y))
        ( refl-htpy)
        ( refl-htpy)

    reassociate' :
      Σ ( type-subuniverse P)
        ( λ A →
          Σ ( type-subuniverse P)
            ( λ B →
              ( ( inclusion-subuniverse
                  ( subuniverse-global-subuniverse Q l3)
                  ( S A)) ×
                inclusion-subuniverse
                  ( subuniverse-global-subuniverse Q l4)
                  ( T B)) ×
              ( (X → H A) × (X → H B)))) ≃
      product-dirichlet-series-species-subuniverse P Q C1 H C2 S T X
    pr1 reassociate' (A , B , (s , t) , (fs , ft)) =
      ((A , (s , fs)) , (B , (t , ft)))
    pr2 reassociate' =
      is-equiv-is-invertible
        ( λ ((A , (s , fs)) , (B , (t , ft))) →
          (A , B , (s , t) , (fs , ft)))
        ( refl-htpy)
        ( refl-htpy)
```
