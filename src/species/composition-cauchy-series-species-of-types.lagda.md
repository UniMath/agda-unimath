# Composition of Cauchy series of species of types

```agda
module species.composition-cauchy-series-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universal-property-cartesian-product-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import species.cauchy-composition-species-of-types
open import species.cauchy-series-species-of-types
open import species.species-of-types
```

</details>

## Idea

The
{{#concept "composition" Disambiguation="of Cauchy series of two species of types" Agda=composition-cauchy-series-species-types}}
of [Cauchy series](species.cauchy-series-species-of-types.md) of two
[species of types](species.species-of-types.md) `S` and `T` at `X` is defined as
the Cauchy series of `S` applied to the Cauchy series of `T` at `X`.

## Definition

```agda
composition-cauchy-series-species-types :
  {l1 l2 l3 l4 : Level} → species-types l1 l2 → species-types l1 l3 →
  UU l4 → UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
composition-cauchy-series-species-types S T X =
  cauchy-series-species-types S (cauchy-series-species-types T X)
```

## Properties

### The Cauchy series associated to the composition of the species `S` and `T` is the composition of their Cauchy series

```agda
module _
  {l1 l2 l3 l4 : Level}
  (S : species-types l1 l2)
  (T : species-types l1 l3)
  (X : UU l4)
  where

  equiv-cauchy-series-composition-species-types :
    cauchy-series-species-types
      ( cauchy-composition-species-types S T)
      ( X) ≃
    composition-cauchy-series-species-types S T X
  equiv-cauchy-series-composition-species-types =
    ( equiv-tot
      ( λ U →
        ( equiv-product-right inv-distributive-Π-Σ) ∘e
        ( inv-left-distributive-product-Σ) ∘e
          ( equiv-tot
            ( λ V →
              ( equiv-product-right
                ( ( inv-equiv-up-product) ∘e
                  ( equiv-product-right equiv-ev-pair))) ∘e
              ( left-unit-law-Σ-is-contr
                ( is-torsorial-equiv' (Σ U V))
                ( Σ U V , id-equiv)))))) ∘e
    ( reassociate)
    where
    reassociate :
      cauchy-series-species-types (cauchy-composition-species-types S T) X ≃
      Σ ( UU l1)
        ( λ U →
          Σ ( U → UU l1)
            ( λ V →
              Σ ( Σ ( UU l1) (λ F → F ≃ Σ U V))
                ( λ F → (S U) × (((y : U) → T (V y)) × (pr1 F → X)))))
    pr1 reassociate (F , ((U , V , e) , s , fs) , ft) =
      (U , V , (F , e) , s , fs , ft)
    pr2 reassociate =
      is-equiv-is-invertible
        ( λ (U , V , (F , e) , s , fs , ft) →
          (F , ((U , V , e) , s , fs) , ft))
        ( refl-htpy)
        ( refl-htpy)
```
