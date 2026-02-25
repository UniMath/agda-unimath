# Small Cauchy composition of species types in subuniverses

```agda
module species.small-cauchy-composition-species-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.relaxed-sigma-decompositions
open import foundation.sigma-closed-subuniverses
open import foundation.sigma-decomposition-subuniverse
open import foundation.small-types
open import foundation.subuniverses
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import species.cauchy-composition-species-of-types
open import species.species-of-types-in-subuniverses
open import species.unit-cauchy-composition-species-of-types
```

</details>

## Idea

A [species](species.species-of-types-in-subuniverses.md)
`S : Inhabited-Type → UU l` can be thought of as the analytic endofunctor

```text
  X ↦ Σ (A : Inhabited-Type), (S A) × (A → X).
```

Using the formula for composition of analytic endofunctors, we obtain a way to
compose species.

## Definition

### Cauchy composition of species

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : subuniverse l1 l2)
  (Q : subuniverse l3 l4)
  (S : species-subuniverse P Q)
  (T : species-subuniverse P Q)
  where

  small-cauchy-composition-species-subuniverse' :
    type-subuniverse P → UU (lsuc l1 ⊔ l2 ⊔ l3)
  small-cauchy-composition-species-subuniverse' X =
    Σ ( Σ-Decomposition-Subuniverse P X)
      ( λ D →
        ( inclusion-subuniverse
          ( Q)
          ( S (subuniverse-indexing-type-Σ-Decomposition-Subuniverse P X D))) ×
        ( (x : indexing-type-Σ-Decomposition-Subuniverse P X D) →
          inclusion-subuniverse
          ( Q)
          ( T (subuniverse-cotype-Σ-Decomposition-Subuniverse P X D x))))

module _
  {l1 l2 l3 l4 : Level}
  (P : subuniverse l1 l2)
  (Q : subuniverse l3 l4)
  (C1 :
    ( S T : species-subuniverse P Q) → (X : type-subuniverse P) →
    is-small l3 (small-cauchy-composition-species-subuniverse' P Q S T X))
  (C2 :
    ( S T : species-subuniverse P Q) → (X : type-subuniverse P) →
    ( is-in-subuniverse Q (type-is-small (C1 S T X))))
  (C3 : is-closed-under-Σ-subuniverse P)
  where

  small-cauchy-composition-species-subuniverse :
    species-subuniverse P Q →
    species-subuniverse P Q →
    species-subuniverse P Q
  small-cauchy-composition-species-subuniverse S T X =
    type-is-small (C1 S T X) , C2 S T X
```

## Properties

### Equivalent form with species of types

```agda
  equiv-small-cauchy-composition-Σ-extension-species-subuniverse :
    ( S : species-subuniverse P Q)
    ( T : species-subuniverse P Q)
    ( X : UU l1) →
    Σ-extension-species-subuniverse P Q
      ( small-cauchy-composition-species-subuniverse S T)
      ( X) ≃
    ( cauchy-composition-species-types
      ( Σ-extension-species-subuniverse P Q S)
      ( Σ-extension-species-subuniverse P Q T)
      ( X))
  equiv-small-cauchy-composition-Σ-extension-species-subuniverse S T X =
    ( equiv-tot
      ( λ D →
        ( equiv-product-right inv-distributive-Π-Σ) ∘e
        ( inv-right-distributive-product-Σ) ∘e
        ( equiv-tot (λ _ → inv-left-distributive-product-Σ)) ∘e
        ( associative-Σ))) ∘e
    ( associative-Σ) ∘e
    ( equiv-Σ-equiv-base
      ( _)
      ( ( equiv-remove-redundant-prop
          ( is-prop-type-Prop (P X))
          ( λ D →
            ( tr
              ( is-in-subuniverse P)
              ( eq-equiv
                ( inv-equiv
                  ( matching-correspondence-Relaxed-Σ-Decomposition (pr1 D))))
              ( C3
                ( indexing-type-Relaxed-Σ-Decomposition (pr1 D) , pr1 (pr2 D))
                ( λ x →
                  ( cotype-Relaxed-Σ-Decomposition (pr1 D) x ,
                    pr2 (pr2 D) x)))))) ∘e
        ( commutative-product) ∘e
        ( equiv-tot
          ( λ p → equiv-total-is-in-subuniverse-Σ-Decomposition P (X , p))))) ∘e
    ( inv-associative-Σ) ∘e
    ( equiv-tot (λ p → inv-equiv-is-small (C1 S T (X , p))))
```

### Unit laws for Cauchy composition of species-subuniverse

```agda
  module _
    (C4 : is-in-subuniverse P (raise-unit l1))
    (C5 :
      (X : UU l1) →
      is-small l3 (is-contr (X)))
    (C6 :
      ( X : type-subuniverse P) →
      ( is-in-subuniverse
          ( Q)
          ( type-is-small (C5 (inclusion-subuniverse P X)))))
    where

    small-cauchy-composition-unit-species-subuniverse :
      species-subuniverse P Q
    small-cauchy-composition-unit-species-subuniverse X =
      type-is-small (C5 (inclusion-subuniverse P X)) , C6 X

    equiv-Σ-extension-small-cauchy-composition-unit-subuniverse :
      (X : UU l1) →
      Σ-extension-species-subuniverse
        ( P)
        ( Q)
        ( small-cauchy-composition-unit-species-subuniverse)
        ( X) ≃
      unit-species-types X
    pr1 (equiv-Σ-extension-small-cauchy-composition-unit-subuniverse X) S =
      map-inv-equiv-is-small
        ( C5 X)
        ( pr2 S)
    pr2 (equiv-Σ-extension-small-cauchy-composition-unit-subuniverse X) =
      is-equiv-is-invertible
        ( λ S →
          ( inv-tr
              ( is-in-subuniverse P)
              ( eq-equiv (equiv-raise-unit-is-contr S))
              ( C4) ,
            map-equiv-is-small (C5 X) S))
        ( λ x → eq-is-prop is-property-is-contr)
        ( λ x →
          eq-pair
            ( eq-is-prop (is-prop-type-Prop (P X)))
            ( eq-is-prop
              ( is-prop-equiv' (equiv-is-small (C5 X)) is-property-is-contr)))

    htpy-left-unit-law-small-cauchy-composition-species-subuniverse :
      ( S : species-subuniverse P Q)
      ( X : type-subuniverse P) →
      inclusion-subuniverse
        ( Q)
        ( small-cauchy-composition-species-subuniverse
          ( small-cauchy-composition-unit-species-subuniverse)
          ( S) X) ≃
      inclusion-subuniverse Q (S X)
    htpy-left-unit-law-small-cauchy-composition-species-subuniverse S X =
      ( inv-equiv (equiv-Σ-extension-species-subuniverse P Q S X)) ∘e
      ( left-unit-law-cauchy-composition-species-types
        ( Σ-extension-species-subuniverse P Q S)
        ( inclusion-subuniverse P X)) ∘e
      ( equiv-tot
        ( λ D →
          equiv-product-left
            ( equiv-Σ-extension-small-cauchy-composition-unit-subuniverse
              ( indexing-type-Relaxed-Σ-Decomposition D)))) ∘e
      ( equiv-small-cauchy-composition-Σ-extension-species-subuniverse
        ( small-cauchy-composition-unit-species-subuniverse)
        ( S)
        ( inclusion-subuniverse P X)) ∘e
      ( equiv-Σ-extension-species-subuniverse P Q
        ( small-cauchy-composition-species-subuniverse
          ( small-cauchy-composition-unit-species-subuniverse)
          ( S))
        ( X))

    left-unit-law-small-cauchy-composition-species-subuniverse :
      ( S : species-subuniverse P Q) →
      small-cauchy-composition-species-subuniverse
        small-cauchy-composition-unit-species-subuniverse
        S ＝ S
    left-unit-law-small-cauchy-composition-species-subuniverse S =
      eq-equiv-fam-subuniverse
      ( Q)
      ( small-cauchy-composition-species-subuniverse
        ( small-cauchy-composition-unit-species-subuniverse)
        ( S))
      ( S)
      ( htpy-left-unit-law-small-cauchy-composition-species-subuniverse S)

    htpy-right-unit-law-small-cauchy-composition-species-subuniverse :
      ( S : species-subuniverse P Q)
      ( X : type-subuniverse P) →
      inclusion-subuniverse
        ( Q)
        ( small-cauchy-composition-species-subuniverse
          ( S)
          ( small-cauchy-composition-unit-species-subuniverse) X) ≃
      inclusion-subuniverse Q (S X)
    htpy-right-unit-law-small-cauchy-composition-species-subuniverse S X =
      ( inv-equiv (equiv-Σ-extension-species-subuniverse P Q S X)) ∘e
      ( right-unit-law-cauchy-composition-species-types
        ( Σ-extension-species-subuniverse P Q S)
        ( inclusion-subuniverse P X)) ∘e
      ( equiv-tot
        ( λ D →
          equiv-product-right
            ( equiv-Π-equiv-family
              ( λ x →
                equiv-Σ-extension-small-cauchy-composition-unit-subuniverse
                  ( cotype-Relaxed-Σ-Decomposition D x))))) ∘e
      ( equiv-small-cauchy-composition-Σ-extension-species-subuniverse
        ( S)
        ( small-cauchy-composition-unit-species-subuniverse)
        ( inclusion-subuniverse P X)) ∘e
      ( equiv-Σ-extension-species-subuniverse P Q
        ( small-cauchy-composition-species-subuniverse S
            small-cauchy-composition-unit-species-subuniverse)
        ( X))

    right-unit-law-small-cauchy-composition-species-subuniverse :
      ( S : species-subuniverse P Q) →
      small-cauchy-composition-species-subuniverse
        S
        small-cauchy-composition-unit-species-subuniverse ＝ S
    right-unit-law-small-cauchy-composition-species-subuniverse S =
      eq-equiv-fam-subuniverse
      ( Q)
      ( small-cauchy-composition-species-subuniverse
        ( S)
        ( small-cauchy-composition-unit-species-subuniverse))
      ( S)
      ( htpy-right-unit-law-small-cauchy-composition-species-subuniverse S)
```

### Associativity of composition of species of types in subuniverse

```agda
  htpy-associative-small-cauchy-composition-species-subuniverse :
    (S : species-subuniverse P Q)
    (T : species-subuniverse P Q)
    (U : species-subuniverse P Q)
    (X : type-subuniverse P) →
    inclusion-subuniverse
      ( Q)
      ( small-cauchy-composition-species-subuniverse
        ( S)
        ( small-cauchy-composition-species-subuniverse T U)
        ( X)) ≃
    inclusion-subuniverse
      ( Q)
      ( small-cauchy-composition-species-subuniverse
        ( small-cauchy-composition-species-subuniverse S T)
        ( U)
        ( X))
  htpy-associative-small-cauchy-composition-species-subuniverse S T U X =
    ( inv-equiv
      ( equiv-Σ-extension-species-subuniverse P Q
        ( small-cauchy-composition-species-subuniverse
          ( small-cauchy-composition-species-subuniverse S T) U)
        ( X))) ∘e
    ( inv-equiv
      ( equiv-small-cauchy-composition-Σ-extension-species-subuniverse
        ( small-cauchy-composition-species-subuniverse S T)
        ( U)
        ( inclusion-subuniverse P X))) ∘e
    ( equiv-tot
      ( λ D →
        equiv-product-left
          ( inv-equiv
            ( equiv-small-cauchy-composition-Σ-extension-species-subuniverse
              ( S)
              ( T)
              ( indexing-type-Relaxed-Σ-Decomposition D))))) ∘e
    ( equiv-associative-cauchy-composition-species-types
      ( Σ-extension-species-subuniverse P Q S)
      ( Σ-extension-species-subuniverse P Q T)
      ( Σ-extension-species-subuniverse P Q U)
      ( inclusion-subuniverse P X)) ∘e
    ( equiv-tot
      ( λ D →
        equiv-product-right
          ( equiv-Π-equiv-family
            ( λ y →
              ( equiv-small-cauchy-composition-Σ-extension-species-subuniverse
                ( T)
                ( U)
                ( cotype-Relaxed-Σ-Decomposition D y)))))) ∘e
    ( equiv-small-cauchy-composition-Σ-extension-species-subuniverse
      ( S)
      ( small-cauchy-composition-species-subuniverse T U)
      ( inclusion-subuniverse P X)) ∘e
    ( equiv-Σ-extension-species-subuniverse P Q
      ( small-cauchy-composition-species-subuniverse
        ( S)
        ( small-cauchy-composition-species-subuniverse T U))
      ( X))

  associative-small-cauchy-composition-species-subuniverse :
    (S : species-subuniverse P Q)
    (T : species-subuniverse P Q)
    (U : species-subuniverse P Q) →
    small-cauchy-composition-species-subuniverse
      ( S)
      ( small-cauchy-composition-species-subuniverse T U) ＝
    small-cauchy-composition-species-subuniverse
      ( small-cauchy-composition-species-subuniverse S T)
      ( U)
  associative-small-cauchy-composition-species-subuniverse S T U =
    eq-equiv-fam-subuniverse
      ( Q)
      ( small-cauchy-composition-species-subuniverse
        ( S)
        ( small-cauchy-composition-species-subuniverse T U))
      ( small-cauchy-composition-species-subuniverse
        ( small-cauchy-composition-species-subuniverse S T)
        ( U))
      ( htpy-associative-small-cauchy-composition-species-subuniverse S T U)
```
