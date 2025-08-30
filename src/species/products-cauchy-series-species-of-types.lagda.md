# Products of Cauchy series of species of types

```agda
module species.products-cauchy-series-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels

open import species.cauchy-products-species-of-types
open import species.cauchy-series-species-of-types
open import species.species-of-types
```

</details>

## Idea

The
{{#concept "product" Disambiguation="of Caucy series of species of types" Agda=product-cauchy-series-species-types}}
of two [Cauchy series](species.cauchy-series-species-of-types.md) of
[species of types in subuniverses](species.species-of-types.md) is just the
pointwise [product](foundation.cartesian-product-types.md).

## Definition

```agda
product-cauchy-series-species-types :
  {l1 l2 l3 l4 : Level} → species-types l1 l2 → species-types l1 l3 →
  UU l4 → UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
product-cauchy-series-species-types S T X =
  cauchy-series-species-types S X × cauchy-series-species-types T X
```

## Properties

### The Cauchy series associated to the Cauchy product of `S` and `T` is equal to the product of theirs Cauchy series

```agda
module _
  {l1 l2 l3 l4 : Level}
  (S : species-types l1 l2)
  (T : species-types l1 l3)
  (X : UU l4)
  where

  equiv-cauchy-series-cauchy-product-species-types :
    cauchy-series-species-types (cauchy-product-species-types S T) X ≃
    product-cauchy-series-species-types S T X
  equiv-cauchy-series-cauchy-product-species-types =
    ( reassociate') ∘e
    ( equiv-tot
      ( λ A →
        equiv-tot
          ( λ B →
            ( equiv-product-right (equiv-universal-property-coproduct X)) ∘e
            ( left-unit-law-Σ-is-contr
              ( is-torsorial-equiv' (A + B))
              ( A + B , id-equiv))))) ∘e
    ( reassociate)
    where
    reassociate :
      cauchy-series-species-types (cauchy-product-species-types S T) X ≃
      Σ ( UU l1)
        ( λ A →
          Σ ( UU l1)
            ( λ B →
              Σ ( Σ ( UU l1) (λ F → F ≃ (A + B)))
                ( λ F → ((S A) × (T B)) × (pr1 F → X))))
    pr1 reassociate (F , ((A , B , e) , x) , y) = (A , B , (F , e) , x , y)
    pr2 reassociate =
      is-equiv-is-invertible
        ( λ (A , B , (F , e) , x , y) → (F , ((A , B , e) , x) , y))
        ( refl-htpy)
        ( refl-htpy)

    reassociate' :
      Σ ( UU l1)
        ( λ A → Σ (UU l1) (λ B → (S A × T B) × ((A → X) × (B → X)))) ≃
      product-cauchy-series-species-types S T X
    pr1 reassociate' (A , B , (s , t) , (fs , ft)) =
      ((A , (s , fs)) , (B , (t , ft)))
    pr2 reassociate' =
      is-equiv-is-invertible
        ( λ ((A , (s , fs)) , (B , (t , ft))) →
          (A , B , (s , t) , (fs , ft)))
        ( refl-htpy)
        ( refl-htpy)
```
