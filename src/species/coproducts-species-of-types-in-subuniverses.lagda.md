# Coproducts of species of types in subuniverses

```agda
module species.coproducts-species-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.global-subuniverses
open import foundation.homotopies
open import foundation.identity-types
open import foundation.subuniverses
open import foundation.universe-levels

open import species.coproducts-species-of-types
open import species.species-of-types-in-subuniverses
```

</details>

## Idea

The
{{#concept "coproduct" Disambiguation="of species of types in subuniverses" Agda=coproduct-species-subuniverse}}
of two
[species of types in subuniverses](species.species-of-types-in-subuniverses.md)
`F` and `G` is the pointwise [coproduct](foundation.coproduct-types.md) provided
that the domain [subuniverse](foundation.subuniverses.md) of `F` and `G` is
stable under coproduct.

## Definitions

### The underlying type of the coproduct of species of types in a subuniverse

```agda
module _
  {l1 l2 l3 l4 : Level} (P : subuniverse l1 l2)
  (Q : global-subuniverse (λ l → l))
  where

  type-coproduct-species-subuniverse :
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
    (X : type-subuniverse P) → UU (l3 ⊔ l4)
  type-coproduct-species-subuniverse S T X =
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q l3)
      ( S X) +
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q l4)
      ( T X)
```

### Subuniverses closed under the coproduct of two species of types in a subuniverse

```agda
is-closed-under-coproduct-species-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) (Q : global-subuniverse (λ l → l)) →
  UUω
is-closed-under-coproduct-species-subuniverse P Q =
  {l3 l4 : Level}
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (X : type-subuniverse P) →
  is-in-subuniverse
    ( subuniverse-global-subuniverse Q (l3 ⊔ l4))
    ( type-coproduct-species-subuniverse P Q S T X)
```

### The coproduct of two species of types in a subuniverse

```agda
module _
  {l1 l2 l3 l4 : Level} (P : subuniverse l1 l2)
  (Q : global-subuniverse (λ l → l))
  (C1 : is-closed-under-coproduct-species-subuniverse P Q)
  where

  coproduct-species-subuniverse :
    species-subuniverse P (subuniverse-global-subuniverse Q l3) →
    species-subuniverse P (subuniverse-global-subuniverse Q l4) →
    species-subuniverse P (subuniverse-global-subuniverse Q (l3 ⊔ l4))
  pr1 (coproduct-species-subuniverse S T X) =
    type-coproduct-species-subuniverse P Q S T X
  pr2 (coproduct-species-subuniverse S T X) = C1 S T X
```

## Properties

### Equivalent form with species of types

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse (λ l → l))
  (C1 : is-closed-under-coproduct-species-subuniverse P Q)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (X : UU l1)
  where

  map-coproduct-Σ-extension-species-subuniverse :
    Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (l3 ⊔ l4))
      ( coproduct-species-subuniverse P Q C1 S T)
      ( X) →
    coproduct-species-types
      ( Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q l3)
          ( S))
      ( Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q l4)
          ( T))
      ( X)
  map-coproduct-Σ-extension-species-subuniverse (p , inl x) = inl (p , x)
  map-coproduct-Σ-extension-species-subuniverse (p , inr x) = inr (p , x)

  map-inv-coproduct-Σ-extension-species-subuniverse :
    coproduct-species-types
      ( Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q l3)
          ( S))
      ( Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q l4)
          ( T))
      ( X) →
    Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (l3 ⊔ l4))
      ( coproduct-species-subuniverse P Q C1 S T)
      ( X)
  map-inv-coproduct-Σ-extension-species-subuniverse (inl x) =
    pr1 x , inl (pr2 x)
  map-inv-coproduct-Σ-extension-species-subuniverse (inr x) =
    pr1 x , inr (pr2 x)

  is-section-map-inv-coproduct-Σ-extension-species-subuniverse :
    ( map-coproduct-Σ-extension-species-subuniverse ∘
      map-inv-coproduct-Σ-extension-species-subuniverse) ~ id
  is-section-map-inv-coproduct-Σ-extension-species-subuniverse (inl (p , x)) =
    refl
  is-section-map-inv-coproduct-Σ-extension-species-subuniverse (inr (p , x)) =
    refl

  is-retraction-map-inv-coproduct-Σ-extension-species-subuniverse :
    ( map-inv-coproduct-Σ-extension-species-subuniverse ∘
      map-coproduct-Σ-extension-species-subuniverse) ~
    id
  is-retraction-map-inv-coproduct-Σ-extension-species-subuniverse (p , inl x) =
    refl
  is-retraction-map-inv-coproduct-Σ-extension-species-subuniverse (p , inr x) =
    refl

  equiv-coproduct-Σ-extension-species-subuniverse :
    Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (l3 ⊔ l4))
      ( coproduct-species-subuniverse P Q C1 S T)
      ( X) ≃
    coproduct-species-types
      ( Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q l3)
          ( S))
      ( Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q l4)
          ( T))
      ( X)
  pr1 equiv-coproduct-Σ-extension-species-subuniverse =
    map-coproduct-Σ-extension-species-subuniverse
  pr2 equiv-coproduct-Σ-extension-species-subuniverse =
    is-equiv-is-invertible
      map-inv-coproduct-Σ-extension-species-subuniverse
      is-section-map-inv-coproduct-Σ-extension-species-subuniverse
      is-retraction-map-inv-coproduct-Σ-extension-species-subuniverse
```
