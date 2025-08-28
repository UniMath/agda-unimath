# Cauchy series of species of types in subuniverses

```agda
module species.cauchy-series-species-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.global-subuniverses
open import foundation.postcomposition-functions
open import foundation.propositions
open import foundation.subuniverses
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import species.cauchy-series-species-of-types
open import species.species-of-types-in-subuniverses
```

</details>

## Idea

The
{{#concept "Cauchy series" Disambiguation="of species of types in subuniverses" Agda=cauchy-series-species-subuniverse}}
of a [species](species.species-of-types-in-subuniverses.md) `S` of types in
[subuniverse](foundation.subuniverses.md) from `P` to `Q` at `X` is defined as

```text
  Σ (U : type-subuniverse P) (S(U) × (U → X)).
```

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : subuniverse l1 l2)
  (Q : subuniverse l3 l4)
  (S : species-subuniverse P Q)
  (X : UU l5)
  where

  cauchy-series-species-subuniverse :
    UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l5)
  cauchy-series-species-subuniverse =
    Σ ( type-subuniverse P)
      ( λ U → inclusion-subuniverse Q (S U) × (inclusion-subuniverse P U → X))
```

## Property

### Equivalent form with species of types

```agda
  equiv-cauchy-series-Σ-extension-species-subuniverse :
    cauchy-series-species-subuniverse ≃
    cauchy-series-species-types (Σ-extension-species-subuniverse P Q S) X
  equiv-cauchy-series-Σ-extension-species-subuniverse =
    ( equiv-tot
      ( λ U →
        inv-associative-Σ
          ( type-Prop (P U))
          ( λ p → inclusion-subuniverse Q (S (U , p)))
          ( λ _ → U → X))) ∘e
    ( associative-Σ
      ( UU l1)
      ( λ U → type-Prop (P U))
      ( λ U → Σ ( inclusion-subuniverse Q (S U)) (λ _ → pr1 U → X)))
```

### Equivalences

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse (λ l → l))
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (f :
    (F : type-subuniverse P) →
    inclusion-subuniverse (subuniverse-global-subuniverse Q l3) (S F) ≃
    inclusion-subuniverse (subuniverse-global-subuniverse Q l4) (T F))
  (X : UU l5)
  where

  equiv-cauchy-series-equiv-species-subuniverse :
    cauchy-series-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q l3)
      ( S)
      ( X) ≃
    cauchy-series-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q l4)
      ( T)
      ( X)
  equiv-cauchy-series-equiv-species-subuniverse =
    equiv-tot (λ X → equiv-product-left (f X))

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (P : subuniverse l1 l2)
  (Q : subuniverse l3 l4)
  (S : species-subuniverse P Q)
  (X : UU l5)
  (Y : UU l6)
  (e : X ≃ Y)
  where

  equiv-cauchy-series-species-subuniverse :
    cauchy-series-species-subuniverse P Q S X ≃
    cauchy-series-species-subuniverse P Q S Y
  equiv-cauchy-series-species-subuniverse =
    equiv-tot
      ( λ F →
        equiv-product-right (equiv-postcomp (inclusion-subuniverse P F) e))
```
