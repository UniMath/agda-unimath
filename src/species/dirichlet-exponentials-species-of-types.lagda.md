# Dirichlet exponentials of a species of types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module species.dirichlet-exponentials-species-of-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.arithmetic-law-product-and-pi-decompositions funext univalence truncations
open import foundation.cartesian-product-types funext univalence
open import foundation.coproduct-decompositions funext univalence truncations
open import foundation.dependent-binomial-theorem funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.functoriality-cartesian-product-types funext
open import foundation.functoriality-dependent-function-types funext univalence
open import foundation.functoriality-dependent-pair-types funext
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.pi-decompositions funext univalence
open import foundation.product-decompositions
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence funext univalence
open import foundation.universe-levels

open import species.coproducts-species-of-types funext univalence truncations
open import species.dirichlet-products-species-of-types funext univalence
open import species.equivalences-species-of-types funext univalence
open import species.species-of-types funext univalence
```

</details>

## Idea

The **Dirichlet exponential** of a species of types `S` is defined as follows:

```text
  X ↦ Σ ((U , V , e) : Π-Decomposition X),  Π (u : U) → S (V u).
```

## Definition

```agda
dirichlet-exponential-species-types :
  {l1 l2 : Level} → species-types l1 l2 → species-types l1 (lsuc l1 ⊔ l2)
dirichlet-exponential-species-types {l1} {l2} S X =
  Σ ( Π-Decomposition l1 l1 X)
    ( λ D →
      ( b : indexing-type-Π-Decomposition D) →
      ( S (cotype-Π-Decomposition D b)))
```

## Properties

### The Dirichlet exponential of the sum of a species is equivalent to the Dirichlet product of the exponential of the two species

```agda
module _
  {l1 l2 l3 : Level}
  (S : species-types l1 l2)
  (T : species-types l1 l3)
  where

  private
    reassociate :
      ( X : UU l1) →
      Σ ( Σ ( binary-product-Decomposition l1 l1 X)
            ( λ d →
              ( Π-Decomposition l1 l1
                ( left-summand-binary-product-Decomposition d)) ×
              ( Π-Decomposition l1 l1
                ( right-summand-binary-product-Decomposition d))))
        ( λ D →
          ( ( b : indexing-type-Π-Decomposition (pr1 (pr2 D))) →
            S ( cotype-Π-Decomposition (pr1 (pr2 D)) b)) ×
          ( ( b : indexing-type-Π-Decomposition (pr2 (pr2 D))) →
            T ( cotype-Π-Decomposition (pr2 (pr2 D)) b))) ≃
      dirichlet-product-species-types
        ( dirichlet-exponential-species-types S)
        ( dirichlet-exponential-species-types T)
        ( X)
    pr1 (reassociate X) ((d , dl , dr) , s , t) =
      ( d , (dl , s) , dr , t)
    pr2 (reassociate X) =
      is-equiv-is-invertible
        ( λ ( d , (dl , s) , dr , t) → ((d , dl , dr) , s , t))
        ( refl-htpy)
        ( refl-htpy)

  equiv-dirichlet-exponential-sum-species-types :
    equiv-species-types
      ( dirichlet-exponential-species-types (coproduct-species-types S T))
      ( dirichlet-product-species-types
        ( dirichlet-exponential-species-types S)
        ( dirichlet-exponential-species-types T))
  equiv-dirichlet-exponential-sum-species-types X =
    ( reassociate X) ∘e
    ( ( equiv-Σ
        ( λ D →
          ( ( b : indexing-type-Π-Decomposition (pr1 (pr2 D))) →
            S (cotype-Π-Decomposition (pr1 (pr2 D)) b)) ×
          ( ( b : indexing-type-Π-Decomposition (pr2 (pr2 D))) →
            T (cotype-Π-Decomposition (pr2 (pr2 D)) b)))
        ( equiv-binary-product-Decomposition-Π-Decomposition)
        ( λ D →
          equiv-product
            ( equiv-Π-equiv-family
              ( λ a' →
                equiv-eq
                  ( ap S
                    ( inv
                      ( compute-left-equiv-binary-product-Decomposition-Π-Decomposition
                        ( D)
                        ( a'))))))
            ( equiv-Π-equiv-family
              ( λ b' →
                equiv-eq
                  ( ap T
                    ( inv
                      ( compute-right-equiv-binary-product-Decomposition-Π-Decomposition
                        ( D)
                        ( b')))))))) ∘e
      ( ( inv-associative-Σ
          ( Π-Decomposition l1 l1 X)
          ( λ d →
            binary-coproduct-Decomposition l1 l1
              ( indexing-type-Π-Decomposition d))
              ( _)) ∘e
        ( equiv-tot
          ( λ d → distributive-Π-coproduct-binary-coproduct-Decomposition))))
```
