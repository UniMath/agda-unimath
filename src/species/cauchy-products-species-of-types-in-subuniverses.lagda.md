# Cauchy products of species of types in subuniverses

```agda
module species.cauchy-products-species-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-decompositions
open import foundation.coproduct-decompositions-subuniverse
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.global-subuniverses
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subuniverses
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import species.cauchy-products-species-of-types
open import species.species-of-types-in-subuniverses
```

</details>

## Idea

The
{{#concept "Cauchy product" Disambiguation="of species of types in subuniverses" Agda=cauchy-product-species-subuniverse}}
of two [species](species.species-of-types-in-subuniverses.md) `S` and `T` from
`P` to `Q` of types in [subuniverses](foundation.subuniverses.md) is defined by

```text
  X ↦ Σ (k : P), Σ (k' : P), Σ (e : k + k' ≃ X), S(k) × T(k').
```

If `Q` is closed under [products](foundation.cartesian-product-types.md) and
[dependent pair types](foundation.dependent-pair-types.md) over types in `P`,
then the Cauchy product is also a species of subuniverses from `P` to `Q`.

## Definition

### The underlying type of the Cauchy product of species in a subuniverse

```agda
module _
  {α : Level → Level} {l1 l2 l3 l4 : Level}
  (P : subuniverse l1 l2) (Q : global-subuniverse α)
  where

  type-cauchy-product-species-subuniverse :
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
    (X : type-subuniverse P) → UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
  type-cauchy-product-species-subuniverse S T X =
    Σ ( binary-coproduct-Decomposition-subuniverse P X)
      ( λ d →
        inclusion-subuniverse
          ( subuniverse-global-subuniverse Q l3)
          ( S (left-summand-binary-coproduct-Decomposition-subuniverse P X d)) ×
        inclusion-subuniverse
          ( subuniverse-global-subuniverse Q l4)
          ( T (right-summand-binary-coproduct-Decomposition-subuniverse P X d)))
```

### Subuniverses closed under the Cauchy product of species in a subuniverse

```agda
is-closed-under-cauchy-product-species-subuniverse :
  {α : Level → Level} {l1 l2 : Level}
  (P : subuniverse l1 l2) (Q : global-subuniverse α) →
  UUω
is-closed-under-cauchy-product-species-subuniverse {α} {l1} {l2} P Q =
  {l3 l4 : Level}
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (X : type-subuniverse P) →
  is-in-subuniverse
    ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
    ( type-cauchy-product-species-subuniverse P Q S T X)
```

### The Cauchy product of species in a subuniverse

```agda
module _
  {α : Level → Level} {l1 l2 l3 l4 : Level}
  (P : subuniverse l1 l2) (Q : global-subuniverse α)
  (C1 : is-closed-under-cauchy-product-species-subuniverse P Q)
  where

  cauchy-product-species-subuniverse :
    species-subuniverse P (subuniverse-global-subuniverse Q l3) →
    species-subuniverse P (subuniverse-global-subuniverse Q l4) →
    species-subuniverse P
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
  pr1 (cauchy-product-species-subuniverse S T X) =
    type-cauchy-product-species-subuniverse P Q S T X
  pr2 (cauchy-product-species-subuniverse S T X) = C1 S T X
```

## Properties

### The Cauchy product is associative

```agda
module _
  {α : Level → Level} {l1 l2 l3 l4 l5 : Level}
  (P : subuniverse l1 l2) (Q : global-subuniverse α)
  (C1 : is-closed-under-cauchy-product-species-subuniverse P Q)
  (C2 : is-closed-under-coproducts-subuniverse P)
  where

  module _
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
    (U : species-subuniverse P (subuniverse-global-subuniverse Q l5))
    (X : type-subuniverse P)
    where

    equiv-left-iterated-cauchy-product-species-subuniverse :
      type-cauchy-product-species-subuniverse P Q
        ( cauchy-product-species-subuniverse P Q C1 S T)
        ( U)
        ( X) ≃
      Σ ( ternary-coproduct-Decomposition-subuniverse P X)
        ( λ d →
          inclusion-subuniverse ( subuniverse-global-subuniverse Q l3)
            ( S
              ( first-summand-ternary-coproduct-Decomposition-subuniverse
                P X d)) ×
            ( inclusion-subuniverse ( subuniverse-global-subuniverse Q l4)
              ( T
                ( second-summand-ternary-coproduct-Decomposition-subuniverse
                  P X d)) ×
              inclusion-subuniverse ( subuniverse-global-subuniverse Q l5)
              ( U
                ( third-summand-ternary-coproduct-Decomposition-subuniverse
                  P X d))))
    equiv-left-iterated-cauchy-product-species-subuniverse =
      ( equiv-Σ
        ( λ d →
          inclusion-subuniverse
            ( subuniverse-global-subuniverse Q l3)
            ( S
              ( first-summand-ternary-coproduct-Decomposition-subuniverse
                  P X d)) ×
            ( inclusion-subuniverse ( subuniverse-global-subuniverse Q l4)
              ( T
                ( second-summand-ternary-coproduct-Decomposition-subuniverse
                    P X d)) ×
              inclusion-subuniverse ( subuniverse-global-subuniverse Q l5)
              ( U
                ( third-summand-ternary-coproduct-Decomposition-subuniverse
                    P X d))))
        ( ( equiv-Σ
            ( _)
            ( associative-product ∘e commutative-product)
            ( λ x →
              equiv-postcomp-equiv
                ( associative-coproduct ∘e commutative-coproduct)
                ( inclusion-subuniverse P X))) ∘e
            ( equiv-ternary-left-iterated-coproduct-Decomposition-subuniverse
                P X C2))
        ( λ d → associative-product)) ∘e
      ( inv-associative-Σ) ∘e
      ( equiv-tot (λ d → right-distributive-product-Σ))

    equiv-right-iterated-cauchy-product-species-subuniverse :
      type-cauchy-product-species-subuniverse P Q
        ( S)
        ( cauchy-product-species-subuniverse P Q C1 T U)
        ( X) ≃
      Σ ( ternary-coproduct-Decomposition-subuniverse P X)
        ( λ d →
          inclusion-subuniverse ( subuniverse-global-subuniverse Q l3)
            ( S
              ( first-summand-ternary-coproduct-Decomposition-subuniverse
                P X d)) ×
            ( inclusion-subuniverse ( subuniverse-global-subuniverse Q l4)
              ( T
                ( second-summand-ternary-coproduct-Decomposition-subuniverse
                  P X d)) ×
              inclusion-subuniverse ( subuniverse-global-subuniverse Q l5)
              ( U
                ( third-summand-ternary-coproduct-Decomposition-subuniverse
                  P X d))))
    equiv-right-iterated-cauchy-product-species-subuniverse =
      ( equiv-Σ-equiv-base
        ( _)
        ( equiv-ternary-right-iterated-coproduct-Decomposition-subuniverse
            P X C2)) ∘e
      ( inv-associative-Σ) ∘e
      ( equiv-tot (λ d → left-distributive-product-Σ))

    equiv-associative-cauchy-product-species-subuniverse :
      type-cauchy-product-species-subuniverse P Q
        ( cauchy-product-species-subuniverse P Q C1 S T)
        ( U)
        ( X) ≃
      type-cauchy-product-species-subuniverse P Q
        ( S)
        ( cauchy-product-species-subuniverse P Q C1 T U)
        ( X)
    equiv-associative-cauchy-product-species-subuniverse =
      inv-equiv (equiv-right-iterated-cauchy-product-species-subuniverse) ∘e
      equiv-left-iterated-cauchy-product-species-subuniverse

  module _
    (S : species-subuniverse P ( subuniverse-global-subuniverse Q l3))
    (T : species-subuniverse P ( subuniverse-global-subuniverse Q l4))
    (U : species-subuniverse P ( subuniverse-global-subuniverse Q l5))
    where

    associative-cauchy-product-species-subuniverse :
      cauchy-product-species-subuniverse P Q C1
        ( cauchy-product-species-subuniverse P Q C1 S T)
        ( U) ＝
      cauchy-product-species-subuniverse P Q C1
        ( S)
        ( cauchy-product-species-subuniverse P Q C1 T U)
    associative-cauchy-product-species-subuniverse =
      eq-equiv-fam-subuniverse
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
        ( cauchy-product-species-subuniverse P Q C1
          ( cauchy-product-species-subuniverse P Q C1 S T)
          ( U))
        ( cauchy-product-species-subuniverse P Q C1
          ( S)
          ( cauchy-product-species-subuniverse P Q C1 T U))
        ( equiv-associative-cauchy-product-species-subuniverse S T U)
```

### The Cauchy product is commutative

```agda
module _
  {α : Level → Level} {l1 l2 l3 l4 : Level}
  (P : subuniverse l1 l2) (Q : global-subuniverse α)
  (C1 : is-closed-under-cauchy-product-species-subuniverse P Q)
  (S : species-subuniverse P ( subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P ( subuniverse-global-subuniverse Q l4))
  where

  equiv-commutative-cauchy-product-species-subuniverse :
    (X : type-subuniverse P) →
    type-cauchy-product-species-subuniverse P Q S T X ≃
    type-cauchy-product-species-subuniverse P Q T S X
  equiv-commutative-cauchy-product-species-subuniverse X =
    equiv-Σ
      ( λ d →
        inclusion-subuniverse ( subuniverse-global-subuniverse Q l4)
          ( T (left-summand-binary-coproduct-Decomposition-subuniverse P X d)) ×
        inclusion-subuniverse ( subuniverse-global-subuniverse Q l3)
          ( S (right-summand-binary-coproduct-Decomposition-subuniverse P X d)))
      ( equiv-commutative-binary-coproduct-Decomposition-subuniverse P X)
      ( λ _ → commutative-product)

  commutative-cauchy-product-species-subuniverse :
    cauchy-product-species-subuniverse P Q C1 S T ＝
    cauchy-product-species-subuniverse P Q C1 T S
  commutative-cauchy-product-species-subuniverse =
    eq-equiv-fam-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
      ( cauchy-product-species-subuniverse P Q C1 S T)
      ( cauchy-product-species-subuniverse P Q C1 T S)
      ( equiv-commutative-cauchy-product-species-subuniverse)
```

### Unit laws of the Cauchy product

```agda
unit-cauchy-product-species-subuniverse :
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (Q : subuniverse l1 l3) →
  ( (X : type-subuniverse P) →
    is-in-subuniverse Q ( is-empty (inclusion-subuniverse P X))) →
  species-subuniverse P Q
unit-cauchy-product-species-subuniverse P Q C X =
  is-empty (inclusion-subuniverse P X) , C X

module _
  {α : Level → Level} {l1 l2 l3 : Level}
  (P : subuniverse l1 l2) (Q : global-subuniverse α)
  (C1 : is-closed-under-cauchy-product-species-subuniverse P Q)
  (C2 : is-in-subuniverse P (raise-empty l1))
  (C3 :
    (X : type-subuniverse P) →
    is-in-subuniverse
      ( subuniverse-global-subuniverse Q l1)
      ( is-empty (inclusion-subuniverse P X)))
  (S : species-subuniverse P ( subuniverse-global-subuniverse Q l3))
  where

  equiv-right-unit-law-cauchy-product-species-subuniverse :
    (X : type-subuniverse P) →
    type-cauchy-product-species-subuniverse P Q
      ( S)
      ( unit-cauchy-product-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l1)
        ( C3))
      ( X) ≃
    inclusion-subuniverse (subuniverse-global-subuniverse Q l3) (S X)
  equiv-right-unit-law-cauchy-product-species-subuniverse X =
    ( left-unit-law-Σ-is-contr
      ( is-torsorial-equiv-subuniverse P X)
      ( X , id-equiv)) ∘e
    ( equiv-Σ-equiv-base
      ( λ p →
        inclusion-subuniverse
          ( subuniverse-global-subuniverse Q l3)
          ( S (pr1 (p))))
      ( equiv-is-empty-right-summand-binary-coproduct-Decomposition-subuniverse
        P
        X
        C2)) ∘e
    ( inv-associative-Σ) ∘e
    ( equiv-tot (λ _ → commutative-product))

  equiv-left-unit-law-cauchy-product-species-subuniverse :
    (X : type-subuniverse P) →
    type-cauchy-product-species-subuniverse P Q
      ( unit-cauchy-product-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l1)
        ( C3))
      ( S)
      ( X) ≃
    inclusion-subuniverse (subuniverse-global-subuniverse Q l3) (S X)
  equiv-left-unit-law-cauchy-product-species-subuniverse X =
    equiv-right-unit-law-cauchy-product-species-subuniverse X ∘e
    equiv-commutative-cauchy-product-species-subuniverse
      ( P)
      ( Q)
      ( C1)
      ( unit-cauchy-product-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l1)
        ( C3))
      ( S)
      ( X)
```

### Equivalent form with species of types

```agda
module _
  {α : Level → Level} {l1 l2 l3 l4 : Level}
  (P : subuniverse l1 l2) (Q : global-subuniverse α)
  (C1 : is-closed-under-cauchy-product-species-subuniverse P Q)
  (C2 : is-closed-under-coproducts-subuniverse P)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (X : UU l1)
  where

  equiv-cauchy-product-Σ-extension-species-subuniverse :
    Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
      ( cauchy-product-species-subuniverse P Q C1 S T)
      ( X) ≃
    cauchy-product-species-types
      ( Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l3)
        ( S))
      ( Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l4)
        ( T))
      ( X)
  equiv-cauchy-product-Σ-extension-species-subuniverse =
    ( reassociate') ∘e
    ( equiv-tot
      ( λ d →
        equiv-Σ-equiv-base
          ( λ p →
            ( inclusion-subuniverse
              ( subuniverse-global-subuniverse Q l3)
              ( S (left-summand-binary-coproduct-Decomposition d , pr1 p))) ×
            ( inclusion-subuniverse
              ( subuniverse-global-subuniverse Q l4)
              ( T (right-summand-binary-coproduct-Decomposition d , pr2 p))))
          ( equiv-remove-redundant-prop
            ( is-prop-type-Prop (P X))
            ( λ p →
              tr
                ( is-in-subuniverse P)
                ( inv
                  ( eq-equiv
                    ( matching-correspondence-binary-coproduct-Decomposition
                      ( d))))
                ( C2 (pr1 p) (pr2 p)))))) ∘e
    ( reassociate)
    where
    reassociate :
      Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
        ( cauchy-product-species-subuniverse P Q C1 S T)
        ( X) ≃
      Σ ( binary-coproduct-Decomposition l1 l1 X)
        ( λ (A , B , e) →
          Σ ( ( is-in-subuniverse P A × is-in-subuniverse P B) ×
              is-in-subuniverse P X)
            ( λ ((pA , pB) , pX) →
              inclusion-subuniverse
                ( subuniverse-global-subuniverse Q l3)
                ( S (A , pA)) ×
              inclusion-subuniverse
                ( subuniverse-global-subuniverse Q l4)
                ( T (B , pB))))
    pr1 reassociate (pX , ((A , pA) , (B , pB) , e) , s , t) =
      (A , B , e) , ((pA , pB) , pX) , (s , t)
    pr2 reassociate = is-equiv-is-invertible
      ( λ ((A , B , e) , ((pA , pB) , pX) , (s , t)) →
        ( pX , ((A , pA) , (B , pB) , e) , s , t))
      ( refl-htpy)
      ( refl-htpy)

    reassociate' :
      Σ ( binary-coproduct-Decomposition l1 l1 X)
        ( λ d →
          Σ ( Σ (pr1 (P (pr1 d))) (λ v → pr1 (P (pr1 (pr2 d)))))
            ( λ p → pr1 (S (pr1 d , pr1 p)) × pr1 (T (pr1 (pr2 d) , pr2 p))))
      ≃
      cauchy-product-species-types
      ( Σ-extension-species-subuniverse P
        ( subuniverse-global-subuniverse Q l3) S)
      ( Σ-extension-species-subuniverse P
        ( subuniverse-global-subuniverse Q l4) T)
      X
    pr1 reassociate' (d , (pA , pB) , s , t) =
      d , (pA , s) , (pB , t)
    pr2 reassociate' =
      is-equiv-is-invertible
        ( λ ( d , (pA , s) , (pB , t)) → (d , (pA , pB) , s , t))
        ( refl-htpy)
        ( refl-htpy)
```
