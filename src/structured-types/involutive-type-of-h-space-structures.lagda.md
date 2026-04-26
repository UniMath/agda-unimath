# The involutive type of H-space structures on a pointed type

```agda
module structured-types.involutive-type-of-h-space-structures where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.symmetric-identity-types
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import structured-types.constant-pointed-maps
open import structured-types.pointed-types

open import univalent-combinatorics.2-element-types
```

</details>

## Idea

We construct the
{{#concept "involutive type of H-space structures" Agda=h-space-Involutive-Type}}
on a pointed type.

## Definition

### The involutive type of H-space structures on a pointed type

```agda
h-space-Involutive-Type :
  {l1 : Level} (A : Pointed-Type l1) (X : 2-Element-Type lzero) → UU l1
h-space-Involutive-Type A X =
  Σ ( (type-2-Element-Type X → type-Pointed-Type A) → type-Pointed-Type A)
    ( λ μ →
      Σ ( ( f : type-2-Element-Type X → type-Pointed-Type A) →
          ( x : type-2-Element-Type X) →
          ( p : f x ＝ point-Pointed-Type A) →
          μ f ＝ f (map-swap-2-Element-Type X x))
        ( λ ν →
          symmetric-Id
            ( ( X) ,
              ( λ x →
                ν ( map-constant-pointed-map (type-2-Element-Type X , x) A)
                  ( x)
                  ( refl)))))
```

## Properties

### Characterization of equality in the involutive type of H-space structures on a pointed type

```agda
module _
  {l1 : Level} (A : Pointed-Type l1) (X : 2-Element-Type lzero)
  where

  htpy-h-space-Involutive-Type :
    (μ μ' : h-space-Involutive-Type A X) → UU l1
  htpy-h-space-Involutive-Type μ μ' =
    Σ ( (f : type-2-Element-Type X → type-Pointed-Type A) → pr1 μ f ＝ pr1 μ' f)
      ( λ H →
        Σ ( ( f : type-2-Element-Type X → type-Pointed-Type A) →
            ( x : type-2-Element-Type X) →
            ( p : f x ＝ point-Pointed-Type A) →
            pr1 (pr2 μ) f x p ＝ (H f ∙ pr1 (pr2 μ') f x p))
          ( λ K →
            Eq-symmetric-Id
              ( ( X) ,
                ( λ x →
                  ( H ( map-constant-pointed-map
                        ( type-2-Element-Type X , x)
                        ( A))) ∙
                  ( pr1
                    ( pr2 μ')
                    ( map-constant-pointed-map (type-2-Element-Type X , x) A)
                    ( x)
                    ( refl))))
              ( tr-symmetric-Id
                ( ( X) ,
                  ( λ x →
                    pr1
                      ( pr2 μ)
                      ( map-constant-pointed-map (type-2-Element-Type X , x) A)
                      ( x)
                      ( refl)))
                ( ( X) ,
                  ( λ x →
                    ( H ( map-constant-pointed-map
                          ( type-2-Element-Type X , x)
                          ( A))) ∙
                    ( pr1
                      ( pr2 μ')
                      ( map-constant-pointed-map (type-2-Element-Type X , x) A)
                        ( x)
                        ( refl))))
                ( id-equiv)
                ( λ x →
                  K ( map-constant-pointed-map (type-2-Element-Type X , x) A)
                    ( x)
                    ( refl))
                ( pr2 (pr2 μ)))
              ( map-equiv-symmetric-Id
                ( equiv-concat
                  ( H ( const
                        ( type-2-Element-Type X)
                        ( point-Pointed-Type A)))
                  ( point-Pointed-Type A))
                ( ( X) ,
                  ( λ x →
                    pr1
                      ( pr2 μ')
                      ( map-constant-pointed-map (type-2-Element-Type X , x) A)
                      ( x)
                      ( refl)))
                ( pr2 (pr2 μ')))))

  refl-htpy-h-space-Involutive-Type :
    (μ : h-space-Involutive-Type A X) → htpy-h-space-Involutive-Type μ μ
  pr1 (refl-htpy-h-space-Involutive-Type (μ , unit-laws-μ , coh-μ)) f = refl
  pr1
    ( pr2 (refl-htpy-h-space-Involutive-Type (μ , unit-laws-μ , coh-μ))) f x p =
    refl
  pr1
    ( pr2 (pr2 (refl-htpy-h-space-Involutive-Type (μ , unit-laws-μ , coh-μ)))) =
    refl
  pr2
    ( pr2
      ( pr2 (refl-htpy-h-space-Involutive-Type (μ , unit-laws-μ , coh-μ)))) x =
    ( ( compute-pr2-tr-symmetric-Id
        ( ( X) ,
          ( λ x →
            unit-laws-μ
              ( map-constant-pointed-map (type-2-Element-Type X , x) A)
              ( x)
              ( refl)))
        ( ( X) ,
          ( λ x →
            unit-laws-μ
              ( map-constant-pointed-map (type-2-Element-Type X , x) A)
              ( x)
              ( refl)))
        ( id-equiv)
        ( λ y → refl)
        ( λ y → pr2 coh-μ y)
        ( x)) ∙
      ( right-unit)) ∙
    ( inv (ap-id (pr2 coh-μ x)))

  abstract
    is-torsorial-htpy-h-space-Involutive-Type :
      ( μ : h-space-Involutive-Type A X) →
      is-torsorial (htpy-h-space-Involutive-Type μ)
    is-torsorial-htpy-h-space-Involutive-Type (μ , ν , ρ) =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy μ)
        ( μ , refl-htpy)
        ( is-torsorial-Eq-structure
          ( is-torsorial-Eq-Π
            ( λ f → is-torsorial-Eq-Π (λ x → is-torsorial-htpy (ν f x))))
          ( ν , (λ f x p → refl))
          ( is-contr-equiv
            ( Σ ( symmetric-Id
                  ( ( X) ,
                    ( λ x →
                      ν ( map-constant-pointed-map
                          ( type-2-Element-Type X , x)
                          ( A))
                        ( x)
                        ( refl))))
                ( Eq-symmetric-Id
                  ( ( X) ,
                    ( λ x →
                      ν ( map-constant-pointed-map
                          ( type-2-Element-Type X , x)
                          ( A))
                        ( x)
                        ( refl)))
                  ( ρ)))
            ( equiv-tot
              ( λ α →
                equiv-binary-tr
                  ( Eq-symmetric-Id
                    ( ( X) ,
                      ( λ x →
                        ν ( map-constant-pointed-map
                            ( type-2-Element-Type X , x)
                            ( A))
                          ( x)
                          ( refl))))
                  ( refl-Eq-unordered-pair-tr-symmetric-Id
                    ( ( X) ,
                      ( λ x →
                        ν ( map-constant-pointed-map
                            ( type-2-Element-Type X , x)
                            ( A))
                          ( x)
                          ( refl)))
                    ( ρ))
                  ( id-equiv-symmetric-Id
                    ( ( X) ,
                      ( λ x →
                        ν ( map-constant-pointed-map
                            ( type-2-Element-Type X , x)
                            ( A))
                          ( x)
                          ( refl)))
                    ( α))))
            ( is-torsorial-Eq-symmetric-Id
              ( ( X) ,
                ( λ x →
                  ν ( map-constant-pointed-map (type-2-Element-Type X , x) A)
                    ( x)
                    ( refl)))
              ( ρ))))

  htpy-eq-h-space-Involutive-Type :
    (μ μ' : h-space-Involutive-Type A X) →
    (μ ＝ μ') → htpy-h-space-Involutive-Type μ μ'
  htpy-eq-h-space-Involutive-Type μ .μ refl =
    refl-htpy-h-space-Involutive-Type μ

  abstract
    is-equiv-htpy-eq-h-space-Involutive-Type :
      (μ μ' : h-space-Involutive-Type A X) →
      is-equiv (htpy-eq-h-space-Involutive-Type μ μ')
    is-equiv-htpy-eq-h-space-Involutive-Type μ =
      fundamental-theorem-id
        ( is-torsorial-htpy-h-space-Involutive-Type μ)
        ( htpy-eq-h-space-Involutive-Type μ)

  extensionality-h-space-Involutive-Type :
    (μ μ' : h-space-Involutive-Type A X) →
    (μ ＝ μ') ≃ htpy-h-space-Involutive-Type μ μ'
  pr1 (extensionality-h-space-Involutive-Type μ μ') =
    htpy-eq-h-space-Involutive-Type μ μ'
  pr2 (extensionality-h-space-Involutive-Type μ μ') =
    is-equiv-htpy-eq-h-space-Involutive-Type μ μ'

  eq-htpy-h-space-Involutive-Type :
    (μ μ' : h-space-Involutive-Type A X) →
    htpy-h-space-Involutive-Type μ μ' → μ ＝ μ'
  eq-htpy-h-space-Involutive-Type μ μ' =
    map-inv-equiv (extensionality-h-space-Involutive-Type μ μ')
```
