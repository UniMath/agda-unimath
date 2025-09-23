# Dirichlet exponentials of species of types in subuniverses

```agda
module species.dirichlet-exponentials-species-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.global-subuniverses
open import foundation.homotopies
open import foundation.pi-decompositions
open import foundation.pi-decompositions-subuniverse
open import foundation.product-decompositions
open import foundation.propositions
open import foundation.subuniverses
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.univalence
open import foundation.universe-levels

open import species.coproducts-species-of-types
open import species.coproducts-species-of-types-in-subuniverses
open import species.dirichlet-exponentials-species-of-types
open import species.dirichlet-products-species-of-types-in-subuniverses
open import species.species-of-types-in-subuniverses
```

</details>

## Idea

The
{{#concept "Dirichlet exponential" Disambiguation="of species of types in subuniverses" Agda=dirichlet-exponential-species-subuniverse}}
of a [species](species.species-of-types-in-subuniverses.md) `S : P → Q` of types
in [subuniverses](foundation.subuniverses.md) is defined by

```text
  X ↦ Σ ((U , V , e) : Π-Decomposition-subuniverse P X),  Π (u : U) → S (V u).
```

If `Q` is a [global subuniverse](foundation.global-subuniverses.md), and if the
previous definition is in `Q`, then the Dirichlet exponential is also a species
of types in subuniverses from `P` to `Q`.

## Definition

### The underlying type of the Dirichlet product of species in a subuniverse

```agda
module _
  {α : Level → Level} {l1 l2 l3 : Level}
  (P : subuniverse l1 l2) (Q : global-subuniverse α)
  where

  type-dirichlet-exponential-species-subuniverse :
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
    (X : type-subuniverse P) → UU (lsuc l1 ⊔ l2 ⊔ l3)
  type-dirichlet-exponential-species-subuniverse S X =
    Σ ( Π-Decomposition-Subuniverse P X)
      ( λ D →
        ( b : indexing-type-Π-Decomposition-Subuniverse P X D) →
        ( inclusion-subuniverse
            ( subuniverse-global-subuniverse Q l3)
            ( S (subuniverse-cotype-Π-Decomposition-Subuniverse P X D b))))
```

### Subuniverses closed under the Dirichlet exponential of a species in a subuniverse

```agda
is-closed-under-dirichlet-exponential-species-subuniverse :
  {α : Level → Level} {l1 l2 : Level}
  (P : subuniverse l1 l2) (Q : global-subuniverse α) →
  UUω
is-closed-under-dirichlet-exponential-species-subuniverse {α} {l1} {l2} P Q =
  {l3 : Level}
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (X : type-subuniverse P) →
  is-in-subuniverse
    ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
    ( type-dirichlet-exponential-species-subuniverse P Q S X)
```

### The Dirichlet exponential of a species of types in a subuniverse

```agda
module _
  {α : Level → Level} {l1 l2 l3 : Level}
  (P : subuniverse l1 l2) (Q : global-subuniverse α)
  (C1 : is-closed-under-dirichlet-exponential-species-subuniverse P Q)
  where

  dirichlet-exponential-species-subuniverse :
    species-subuniverse P (subuniverse-global-subuniverse Q l3) →
    species-subuniverse P (subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
  pr1 (dirichlet-exponential-species-subuniverse S X) =
    type-dirichlet-exponential-species-subuniverse P Q S X
  pr2 (dirichlet-exponential-species-subuniverse S X) = C1 S X
```

## Propositions

### Equivalence form with species of types

```agda
module _
  {α : Level → Level} {l1 l2 l3 : Level}
  (P : subuniverse l1 l2) (Q : global-subuniverse α)
  (C1 : is-closed-under-dirichlet-exponential-species-subuniverse P Q)
  (C2 :
    ( U : UU l1) →
    ( V : U → UU l1) →
    ( (u : U) → is-in-subuniverse P (V u)) →
    is-in-subuniverse P (Π U V) → is-in-subuniverse P U)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (X : type-subuniverse P)
  where

  equiv-dirichlet-exponential-Σ-extension-species-subuniverse :
    Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
      ( dirichlet-exponential-species-subuniverse P Q C1 S)
      ( inclusion-subuniverse P X) ≃
    dirichlet-exponential-species-types
      ( Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l3)
        ( S))
      ( inclusion-subuniverse P X)
  equiv-dirichlet-exponential-Σ-extension-species-subuniverse =
    ( reassociate') ∘e
    ( equiv-tot
        ( λ d →
          equiv-Σ-equiv-base
            ( λ p →
              ( u : indexing-type-Π-Decomposition d) →
              inclusion-subuniverse
                ( subuniverse-global-subuniverse Q l3)
                ( S (cotype-Π-Decomposition d u , p u)))
            ( ( equiv-remove-redundant-prop
                ( is-prop-type-Prop (P (indexing-type-Π-Decomposition d)))
                ( λ pV →
                  C2
                    ( indexing-type-Π-Decomposition d)
                    ( cotype-Π-Decomposition d)
                    ( pV)
                    ( tr
                      ( is-in-subuniverse P)
                      ( eq-equiv (matching-correspondence-Π-Decomposition d))
                      ( pr2 X)))) ∘e
              ( commutative-product) ∘e
              ( equiv-remove-redundant-prop
                ( is-prop-type-Prop (P (inclusion-subuniverse P X)))
                ( λ _ → pr2 X))))) ∘e
      ( reassociate)
    where
    reassociate :
      Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
        ( dirichlet-exponential-species-subuniverse P Q C1 S)
        ( inclusion-subuniverse P X) ≃
      Σ ( Π-Decomposition l1 l1 (inclusion-subuniverse P X))
        ( λ (U , V , e) →
          Σ ( ( is-in-subuniverse P U × ((u : U) → is-in-subuniverse P (V u))) ×
              is-in-subuniverse P (inclusion-subuniverse P X))
            ( λ p → (u : U) → pr1 (S (V u , (pr2 (pr1 p)) u))))
    pr1 reassociate (pX , ((U , pU) , V , e) , s) =
      ((U , ((λ u → pr1 (V u)) , e)) , ((pU , (λ u → pr2 (V u))) , pX) , s)
    pr2 reassociate =
      is-equiv-is-invertible
        ( λ ((U , V , e) , ( ((pU , pV) , pX) , s)) →
          ( pX , ((U , pU) , (λ u → V u , pV u) , e) , s))
        ( refl-htpy)
        ( refl-htpy)

    reassociate' :
      Σ ( Π-Decomposition l1 l1 (inclusion-subuniverse P X))
        ( λ d →
          Σ ( ( u : (indexing-type-Π-Decomposition d)) →
              is-in-subuniverse P (cotype-Π-Decomposition d u))
            ( λ p →
              ( ( u : indexing-type-Π-Decomposition d) →
                inclusion-subuniverse
                  ( subuniverse-global-subuniverse Q l3)
                  ( S (cotype-Π-Decomposition d u , p u)))))
        ≃
        dirichlet-exponential-species-types
          ( Σ-extension-species-subuniverse
              ( P)
              ( subuniverse-global-subuniverse Q l3)
              ( S))
        ( inclusion-subuniverse P X)
    pr1 reassociate' (d , pV , s) = d , ( λ u → (pV u) , (s u))
    pr2 reassociate' =
      is-equiv-is-invertible
        ( λ (d , f) → (d , pr1 ∘ f , pr2 ∘ f))
        ( refl-htpy)
        ( refl-htpy)
```

### The Dirichlet exponential of the sum of a species is equivalent to the Dirichlet product of the exponential of the two species

```agda
module _
  {α : Level → Level} {l1 l2 l3 l4 : Level}
  (P : subuniverse l1 l2) (Q : global-subuniverse α)
  (C1 : is-closed-under-dirichlet-exponential-species-subuniverse P Q)
  (C2 : is-closed-under-coproduct-species-subuniverse P Q)
  (C3 : is-closed-under-dirichlet-product-species-subuniverse P Q)
  (C4 :
    ( U : UU l1) →
    ( V : U → UU l1) →
    ( (u : U) → is-in-subuniverse P (V u)) →
      ( is-in-subuniverse P (Π U V)) →
      ( is-in-subuniverse P U))
  (C5 : is-closed-under-products-subuniverse P)
  (C6 :
    ( A B : UU l1) →
    is-in-subuniverse P (A × B) →
    is-in-subuniverse P A × is-in-subuniverse P B)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (X : type-subuniverse P)
  where

  equiv-dirichlet-exponential-sum-species-subuniverse :
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
      ( dirichlet-exponential-species-subuniverse P Q C1
        ( coproduct-species-subuniverse P Q C2 S T) X) ≃
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
      ( dirichlet-product-species-subuniverse P Q C3
        ( dirichlet-exponential-species-subuniverse P Q C1 S)
        ( dirichlet-exponential-species-subuniverse P Q C1 T)
        ( X))
  equiv-dirichlet-exponential-sum-species-subuniverse =
    ( inv-equiv
      ( equiv-Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
        ( dirichlet-product-species-subuniverse P Q C3
          ( dirichlet-exponential-species-subuniverse P Q C1 S)
          ( dirichlet-exponential-species-subuniverse P Q C1 T))
        ( X))) ∘e
    ( inv-equiv
      ( equiv-dirichlet-product-Σ-extension-species-subuniverse P Q C3 C5
        ( dirichlet-exponential-species-subuniverse P Q C1 S)
        ( dirichlet-exponential-species-subuniverse P Q C1 T)
        ( inclusion-subuniverse P X))) ∘e
    ( equiv-tot
      ( λ d →
        equiv-product
          ( inv-equiv
            ( equiv-dirichlet-exponential-Σ-extension-species-subuniverse
              ( P)
              ( Q)
              ( C1)
              ( C4)
              ( S)
              ( left-summand-binary-product-Decomposition d ,
                pr1 (lemma-C6 d))))
          ( inv-equiv
            ( equiv-dirichlet-exponential-Σ-extension-species-subuniverse
              ( P)
              ( Q)
              ( C1)
              ( C4)
              ( T)
              ( right-summand-binary-product-Decomposition d ,
                pr2 (lemma-C6 d)))))) ∘e
    ( equiv-dirichlet-exponential-sum-species-types
      ( Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l3)
        ( S))
      ( Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l4)
        ( T))
      ( pr1 X)) ∘e
    ( equiv-tot
      ( λ d →
        equiv-Π-equiv-family
          ( λ x →
            equiv-coproduct-Σ-extension-species-subuniverse P Q C2 S T
              ( cotype-Π-Decomposition d x)))) ∘e
    ( equiv-dirichlet-exponential-Σ-extension-species-subuniverse P Q C1 C4
      ( coproduct-species-subuniverse P Q C2 S T)
      ( X)) ∘e
    ( equiv-Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
      ( dirichlet-exponential-species-subuniverse P Q C1
        ( coproduct-species-subuniverse P Q C2 S T))
      ( X))
    where
    lemma-C6 =
      λ d →
      C6
        ( left-summand-binary-product-Decomposition d)
        ( right-summand-binary-product-Decomposition d)
        ( tr
          ( is-in-subuniverse P)
          ( eq-equiv (matching-correspondence-binary-product-Decomposition d))
          ( pr2 X))
```
