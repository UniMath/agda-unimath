# Cauchy exponentials of species of types

```agda
module species.cauchy-exponentials-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.arithmetic-law-coproduct-and-sigma-decompositions
open import foundation.cartesian-product-types
open import foundation.coproduct-decompositions
open import foundation.dependent-binomial-theorem
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.relaxed-sigma-decompositions
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import species.cauchy-composition-species-of-types
open import species.cauchy-products-species-of-types
open import species.coproducts-species-of-types
open import species.equivalences-species-of-types
open import species.species-of-types
```

</details>

## Idea

The
{{#concept "Cauchy exponential" Disambiguation="of species of types" Agda=cauchy-exponential-species-types}}
of a [species of types](species.species-of-types.md) `S` can be thought of as
the [Cauchy composite](species.cauchy-composition-species-of-types.md)
`exp ∘ S`. Since the exponent species is defined as `X ↦ 𝟙`, the coefficients of
the Cauchy exponential of `S` is defined as the following species of types:

```text
  X ↦ Σ ((U , V , e) : Relaxed-Σ-Decomposition X), Π (u : U) → S (V u).
```

## Definition

```agda
cauchy-exponential-species-types :
  {l1 l2 : Level} → species-types l1 l2 → species-types l1 (lsuc l1 ⊔ l2)
cauchy-exponential-species-types {l1} {l2} S X =
  Σ ( Relaxed-Σ-Decomposition l1 l1 X)
    ( λ D →
      ( b : indexing-type-Relaxed-Σ-Decomposition D) →
      ( S (cotype-Relaxed-Σ-Decomposition D b)))
```

## Propositions

### The Cauchy exponential in term of composition

```agda
module _
  {l1 l2 : Level}
  (S : species-types l1 l2)
  (X : UU l1)
  where

  equiv-cauchy-exponential-composition-unit-species-types :
    cauchy-composition-species-types (λ _ → unit) S X ≃
    cauchy-exponential-species-types S X
  equiv-cauchy-exponential-composition-unit-species-types =
    equiv-tot (λ _ → left-unit-law-product)
```

### The Cauchy exponential of the sum of a species is equivalent to the Cauchy product of the exponential of the two species

```agda
module _
  {l1 l2 l3 : Level}
  (S : species-types l1 l2)
  (T : species-types l1 l3)
  where

  equiv-cauchy-exponential-sum-species-types :
    equiv-species-types
      ( cauchy-exponential-species-types (coproduct-species-types S T))
      ( cauchy-product-species-types
        ( cauchy-exponential-species-types S)
        ( cauchy-exponential-species-types T))
  equiv-cauchy-exponential-sum-species-types X =
    ( reassociate X) ∘e
    ( equiv-Σ
      ( λ D →
        ( ( b : indexing-type-Relaxed-Σ-Decomposition (pr1 (pr2 D))) →
          S (cotype-Relaxed-Σ-Decomposition (pr1 (pr2 D)) b)) ×
        ( ( b : indexing-type-Relaxed-Σ-Decomposition (pr2 (pr2 D))) →
          T (cotype-Relaxed-Σ-Decomposition (pr2 (pr2 D)) b)))
      ( equiv-binary-coproduct-Decomposition-Σ-Decomposition)
      ( λ D →
        equiv-product
          ( equiv-Π-equiv-family
            ( λ a' →
              equiv-eq
                ( ap S
                  ( inv
                    ( compute-left-equiv-binary-coproduct-Decomposition-Σ-Decomposition
                      ( D)
                      ( a'))))))
          ( equiv-Π-equiv-family
            ( λ b' →
              equiv-eq
                ( ap T
                  ( inv
                    ( compute-right-equiv-binary-coproduct-Decomposition-Σ-Decomposition
                      ( D)
                      ( b')))))))) ∘e
    ( inv-associative-Σ) ∘e
    ( equiv-tot (λ d → distributive-Π-coproduct-binary-coproduct-Decomposition))
    where
    reassociate :
      ( X : UU l1) →
      Σ ( Σ ( binary-coproduct-Decomposition l1 l1 X)
            ( λ d →
              ( Relaxed-Σ-Decomposition l1 l1
                ( left-summand-binary-coproduct-Decomposition d)) ×
              ( Relaxed-Σ-Decomposition l1 l1
                ( right-summand-binary-coproduct-Decomposition d))))
        ( λ D →
          ( ( b : indexing-type-Relaxed-Σ-Decomposition (pr1 (pr2 D))) →
            S ( cotype-Relaxed-Σ-Decomposition (pr1 (pr2 D)) b)) ×
          ( ( b : indexing-type-Relaxed-Σ-Decomposition (pr2 (pr2 D))) →
            T ( cotype-Relaxed-Σ-Decomposition (pr2 (pr2 D)) b))) ≃
      cauchy-product-species-types
        ( cauchy-exponential-species-types S)
        ( cauchy-exponential-species-types T)
        ( X)
    pr1 (reassociate X) ((d , dl , dr) , s , t) =
      ( d , (dl , s) , dr , t)
    pr2 (reassociate X) =
      is-equiv-is-invertible
        ( λ ( d , (dl , s) , dr , t) → ((d , dl , dr) , s , t))
        ( refl-htpy)
        ( refl-htpy)
```
