# Dirichlet products of species of types in subuniverses

```agda
module species.dirichlet-products-species-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.product-decomposition-subuniverse
open import foundation.subuniverses
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import species.species-of-types-in-subuniverses
```

</details>

## Idea

The Dirichlet product of two species of subuniverse `S` and `T` from `P` to `Q`
on `X` is defined as

```text
  Σ (k : P) (Σ (k' : P) (Σ (e : k × k' ≃ X) S(k) × T(k')))
```

If `Q` is stable by product and dependent pair type over `P` type, then the
dirichlet product is also a species of subuniverse from `P` to `Q`

## Definition

### The underlying type of the Dirichlet product of species in a subuniverse

```agda
module _
  {l1 l2 l3 l4 : Level} (P : subuniverse l1 l2) (Q : global-subuniverse id)
  where

  type-dirichlet-product-species-subuniverse :
    (S : species-subuniverse P ( subuniverse-global-subuniverse Q l3))
    (T : species-subuniverse P ( subuniverse-global-subuniverse Q l4))
    (X : type-subuniverse P) → UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
  type-dirichlet-product-species-subuniverse S T X =
    Σ ( binary-product-Decomposition P X)
      ( λ d →
        inclusion-subuniverse ( subuniverse-global-subuniverse Q l3)
          ( S (left-summand-binary-product-Decomposition P X d)) ×
        inclusion-subuniverse ( subuniverse-global-subuniverse Q l4)
          ( T (right-summand-binary-product-Decomposition P X d)))
```

### Subuniverses closed under the Dirichlet product of species in a subuniverse

```agda
is-closed-under-dirichlet-product-species-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) (Q : global-subuniverse id) →
  UUω
is-closed-under-dirichlet-product-species-subuniverse {l1} {l2} P Q =
  {l3 l4 : Level}
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (X : type-subuniverse P) →
  is-in-subuniverse
    ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
    ( type-dirichlet-product-species-subuniverse P Q S T X)
```

### The Dirichlet product of species of types in a subuniverse

```agda
module _
  {l1 l2 l3 l4 : Level} (P : subuniverse l1 l2) (Q : global-subuniverse id)
  ( C1 : is-closed-under-dirichlet-product-species-subuniverse P Q)
  where

  dirichlet-product-species-subuniverse :
    species-subuniverse P ( subuniverse-global-subuniverse Q l3) →
    species-subuniverse P ( subuniverse-global-subuniverse Q l4) →
    species-subuniverse P
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
  pr1 (dirichlet-product-species-subuniverse S T X) =
    type-dirichlet-product-species-subuniverse P Q S T X
  pr2 (dirichlet-product-species-subuniverse S T X) = C1 S T X
```

## Properties

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (P : subuniverse l1 l2) (Q : global-subuniverse id)
  ( C1 : is-closed-under-dirichlet-product-species-subuniverse P Q)
  ( C2 : is-closed-under-products-subuniverse P)
  where

  module _
    (S : species-subuniverse P ( subuniverse-global-subuniverse Q l3))
    (T : species-subuniverse P ( subuniverse-global-subuniverse Q l4))
    (U : species-subuniverse P ( subuniverse-global-subuniverse Q l5))
    (X : type-subuniverse P)
    where

    equiv-left-iterated-dirichlet-product-species-subuniverse :
      type-dirichlet-product-species-subuniverse P Q
        ( dirichlet-product-species-subuniverse P Q C1 S T)
        ( U)
        ( X) ≃
      Σ ( ternary-product-Decomposition P X)
        ( λ d →
          inclusion-subuniverse ( subuniverse-global-subuniverse Q l3)
            ( S (first-summand-ternary-product-Decomposition P X d)) ×
            ( inclusion-subuniverse ( subuniverse-global-subuniverse Q l4)
              ( T (second-summand-ternary-product-Decomposition P X d)) ×
              inclusion-subuniverse ( subuniverse-global-subuniverse Q l5)
              ( U (third-summand-ternary-product-Decomposition P X d))))
    equiv-left-iterated-dirichlet-product-species-subuniverse =
      ( ( equiv-Σ
          ( λ d →
            inclusion-subuniverse ( subuniverse-global-subuniverse Q l3)
            ( S (first-summand-ternary-product-Decomposition P X d)) ×
            ( inclusion-subuniverse ( subuniverse-global-subuniverse Q l4)
              ( T (second-summand-ternary-product-Decomposition P X d)) ×
              inclusion-subuniverse ( subuniverse-global-subuniverse Q l5)
              ( U (third-summand-ternary-product-Decomposition P X d)))))
          ( ( equiv-Σ
              ( _)
              ( associative-prod _ _ _ ∘e commutative-prod)
              ( λ x →
                equiv-postcomp-equiv
                  ( ( associative-prod _ _ _ ∘e
                    ( commutative-prod)))
                  ( inclusion-subuniverse P X)) ∘e
              equiv-ternary-left-iterated-product-Decomposition P X C2))
          ( λ d → associative-prod _ _ _) ∘e
        ( ( inv-associative-Σ
            ( binary-product-Decomposition P X)
            ( λ z → binary-product-Decomposition P (pr1 z))
            ( _)) ∘e
          ( ( equiv-tot λ d → right-distributive-prod-Σ))))

    equiv-right-iterated-dirichlet-product-species-subuniverse :
      type-dirichlet-product-species-subuniverse P Q
        ( S)
        ( dirichlet-product-species-subuniverse P Q C1 T U)
        ( X) ≃
      Σ ( ternary-product-Decomposition P X)
        ( λ d →
          inclusion-subuniverse ( subuniverse-global-subuniverse Q l3)
            ( S (first-summand-ternary-product-Decomposition P X d)) ×
            ( inclusion-subuniverse ( subuniverse-global-subuniverse Q l4)
              ( T (second-summand-ternary-product-Decomposition P X d)) ×
                inclusion-subuniverse ( subuniverse-global-subuniverse Q l5)
              ( U (third-summand-ternary-product-Decomposition P X d))))
    equiv-right-iterated-dirichlet-product-species-subuniverse =
      ( ( equiv-Σ-equiv-base
          ( _)
          ( equiv-ternary-right-iterated-product-Decomposition P X C2)) ∘e
        ( ( inv-associative-Σ
            ( binary-product-Decomposition P X)
            ( λ z → binary-product-Decomposition P (pr1 (pr2 z)))
            ( _)) ∘e
          ( ( equiv-tot (λ d → left-distributive-prod-Σ)))))

    equiv-associative-dirichlet-product-species-subuniverse :
      type-dirichlet-product-species-subuniverse P Q
        ( dirichlet-product-species-subuniverse P Q C1 S T)
        ( U)
        ( X) ≃
      type-dirichlet-product-species-subuniverse P Q
        ( S)
        ( dirichlet-product-species-subuniverse P Q C1 T U)
        ( X)
    equiv-associative-dirichlet-product-species-subuniverse =
      inv-equiv (equiv-right-iterated-dirichlet-product-species-subuniverse) ∘e
      equiv-left-iterated-dirichlet-product-species-subuniverse

  module _
    (S : species-subuniverse P ( subuniverse-global-subuniverse Q l3))
    (T : species-subuniverse P ( subuniverse-global-subuniverse Q l4))
    (U : species-subuniverse P ( subuniverse-global-subuniverse Q l5))
    where

    associative-dirichlet-product-species-subuniverse :
      dirichlet-product-species-subuniverse P Q C1
        ( dirichlet-product-species-subuniverse P Q C1 S T)
        ( U) ＝
      dirichlet-product-species-subuniverse P Q C1
        ( S)
        ( dirichlet-product-species-subuniverse P Q C1 T U)
    associative-dirichlet-product-species-subuniverse =
      eq-equiv-fam-subuniverse
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
        ( dirichlet-product-species-subuniverse P Q C1
          ( dirichlet-product-species-subuniverse P Q C1 S T)
          ( U))
        ( dirichlet-product-species-subuniverse P Q C1
          ( S)
          ( dirichlet-product-species-subuniverse P Q C1 T U))
        ( equiv-associative-dirichlet-product-species-subuniverse S T U)
```

### Dirichlet product is commutative

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse id)
  (C1 : is-closed-under-dirichlet-product-species-subuniverse P Q)
  (S : species-subuniverse P ( subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P ( subuniverse-global-subuniverse Q l4))
  where

  equiv-commutative-dirichlet-product-species-subuniverse :
    (X : type-subuniverse P) →
    type-dirichlet-product-species-subuniverse P Q S T X ≃
    type-dirichlet-product-species-subuniverse P Q T S X
  equiv-commutative-dirichlet-product-species-subuniverse X =
    equiv-Σ
      ( λ d →
        inclusion-subuniverse ( subuniverse-global-subuniverse Q l4)
          ( T (left-summand-binary-product-Decomposition P X d)) ×
        inclusion-subuniverse ( subuniverse-global-subuniverse Q l3)
          ( S (right-summand-binary-product-Decomposition P X d)))
      ( equiv-commutative-binary-product-Decomposition P X)
      ( λ _ → commutative-prod)

  commutative-dirichlet-product-species-subuniverse :
    dirichlet-product-species-subuniverse P Q C1 S T ＝
    dirichlet-product-species-subuniverse P Q C1 T S
  commutative-dirichlet-product-species-subuniverse =
    eq-equiv-fam-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
      ( dirichlet-product-species-subuniverse P Q C1 S T)
      ( dirichlet-product-species-subuniverse P Q C1 T S)
      ( equiv-commutative-dirichlet-product-species-subuniverse)
```

### Unit laws of Dirichlet product

```agda
unit-dirichlet-product-species-subuniverse :
  {l1 l2 l3 : Level} →
  (P : subuniverse l1 l2) (Q : subuniverse l1 l3) →
  ( (X : type-subuniverse P) →
    is-in-subuniverse Q ( is-contr (inclusion-subuniverse P X))) →
  species-subuniverse P Q
unit-dirichlet-product-species-subuniverse P Q C X =
  is-contr (inclusion-subuniverse P X) , C X

module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (Q : global-subuniverse id)
  (C1 : is-closed-under-dirichlet-product-species-subuniverse P Q)
  (C2 : is-in-subuniverse P (raise-unit l1))
  (C3 :
    (X : type-subuniverse P) →
    is-in-subuniverse
      ( subuniverse-global-subuniverse Q l1)
      ( is-contr (inclusion-subuniverse P X)))
  (S : species-subuniverse P ( subuniverse-global-subuniverse Q l3))
  where

  equiv-right-unit-law-dirichlet-product-species-subuniverse :
    (X : type-subuniverse P) →
    type-dirichlet-product-species-subuniverse P Q
      ( S)
      ( unit-dirichlet-product-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l1)
        ( C3))
      ( X) ≃
    inclusion-subuniverse (subuniverse-global-subuniverse Q l3) (S X)
  equiv-right-unit-law-dirichlet-product-species-subuniverse X =
    ( ( left-unit-law-Σ-is-contr
        ( is-contr-total-equiv-subuniverse P X)
        ( X , id-equiv)) ∘e
      ( ( equiv-Σ-equiv-base
          ( λ p →
            inclusion-subuniverse
              ( subuniverse-global-subuniverse Q l3)
              ( S (pr1 (p))))
          ( equiv-is-contr-right-summand-binary-product-Decomposition
            P
            X
            C2)) ∘e
        ( ( inv-associative-Σ
            ( binary-product-Decomposition P X)
            ( λ d →
              inclusion-subuniverse
                ( subuniverse-global-subuniverse Q l1)
                ( unit-dirichlet-product-species-subuniverse
                  ( P)
                  ( subuniverse-global-subuniverse Q l1)
                  ( C3)
                  ( right-summand-binary-product-Decomposition P X d)))
            ( λ z →
              inclusion-subuniverse
                ( subuniverse-global-subuniverse Q l3)
                ( S
                  ( left-summand-binary-product-Decomposition
                    P
                    X
                    (pr1 z))))) ∘e
          ( ( equiv-tot (λ _ → commutative-prod))))))

  equiv-left-unit-law-dirichlet-product-species-subuniverse :
    (X : type-subuniverse P) →
    type-dirichlet-product-species-subuniverse P Q
      ( unit-dirichlet-product-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l1)
        ( C3))
      ( S)
      ( X) ≃
    inclusion-subuniverse (subuniverse-global-subuniverse Q l3) (S X)
  equiv-left-unit-law-dirichlet-product-species-subuniverse X =
    equiv-right-unit-law-dirichlet-product-species-subuniverse X ∘e
    equiv-commutative-dirichlet-product-species-subuniverse
      ( P)
      ( Q)
      ( C1)
      ( unit-dirichlet-product-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l1)
        ( C3))
      ( S)
      ( X)
```
