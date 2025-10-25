# Precomposition of functions into subuniverses

```agda
module foundation.precomposition-functions-into-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.precomposition-functions
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.sets
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Definitions

```agda
module _
  {α : Level → Level} (𝒫 : {l : Level} → UU l → UU (α l))
  {l1 l2 : Level} (A : Σ (UU l1) 𝒫) (B : Σ (UU l2) 𝒫) (f : pr1 A → pr1 B)
  where

  universal-property-equiv-structured-type : UUω
  universal-property-equiv-structured-type =
    {l : Level} (C : Σ (UU l) 𝒫) → is-equiv (precomp f (pr1 C))
```

## Theorem

### A map between structured types is an equivalence if precomposition of functions into structured types by that map is an equivalence

```agda
module _
  {α : Level → Level} (𝒫 : {l : Level} → UU l → UU (α l))
  {l1 l2 : Level} (A : Σ (UU l1) 𝒫) (B : Σ (UU l2) 𝒫) (f : pr1 A → pr1 B)
  (H : universal-property-equiv-structured-type 𝒫 A B f)
  where

  map-inv-is-equiv-precomp-structured-type : pr1 B → pr1 A
  map-inv-is-equiv-precomp-structured-type =
    pr1 (center (is-contr-map-is-equiv (H A) id))

  is-section-map-inv-is-equiv-precomp-structured-type :
    is-section f map-inv-is-equiv-precomp-structured-type
  is-section-map-inv-is-equiv-precomp-structured-type =
    htpy-eq
      ( ap
        ( pr1)
        ( eq-is-contr'
          ( is-contr-map-is-equiv (H B) f)
          ( ( f ∘ (pr1 (center (is-contr-map-is-equiv (H A) id)))) ,
            ( ap
              ( λ g → f ∘ g)
              ( pr2 (center (is-contr-map-is-equiv (H A) id)))))
          ( id , refl)))

  is-retraction-map-inv-is-equiv-precomp-structured-type :
    is-retraction f map-inv-is-equiv-precomp-structured-type
  is-retraction-map-inv-is-equiv-precomp-structured-type =
    htpy-eq (pr2 (center (is-contr-map-is-equiv (H A) id)))

  abstract
    is-equiv-is-equiv-precomp-structured-type : is-equiv f
    is-equiv-is-equiv-precomp-structured-type =
      is-equiv-is-invertible
        ( map-inv-is-equiv-precomp-structured-type)
        ( is-section-map-inv-is-equiv-precomp-structured-type)
        ( is-retraction-map-inv-is-equiv-precomp-structured-type)
```

## Corollaries

### A map between propositions is an equivalence if precomposition of functions into propositions by that map is an equivalence

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) (f : type-Prop P → type-Prop Q)
  where

  universal-property-equiv-Prop : UUω
  universal-property-equiv-Prop =
    {l : Level} (R : Prop l) → is-equiv (precomp f (type-Prop R))

  is-equiv-is-equiv-precomp-Prop :
    universal-property-equiv-Prop → is-equiv f
  is-equiv-is-equiv-precomp-Prop =
    is-equiv-is-equiv-precomp-structured-type is-prop P Q f
```

### A map between sets is an equivalence if precomposition of functions into sets by that map is an equivalence

```agda
module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2) (f : type-Set A → type-Set B)
  where

  universal-property-equiv-Set : UUω
  universal-property-equiv-Set =
    {l : Level} (C : Set l) → is-equiv (precomp f (type-Set C))

  is-equiv-is-equiv-precomp-Set :
    universal-property-equiv-Set → is-equiv f
  is-equiv-is-equiv-precomp-Set =
    is-equiv-is-equiv-precomp-structured-type is-set A B f
```

### A map between truncated types is an equivalence if precomposition of functions into truncated types by that map is an equivalence

```agda
module _
  {l1 l2 : Level} (k : 𝕋)
  (A : Truncated-Type l1 k) (B : Truncated-Type l2 k)
  (f : type-Truncated-Type A → type-Truncated-Type B)
  where

  universal-property-equiv-Truncated-Type : UUω
  universal-property-equiv-Truncated-Type =
    {l : Level} (C : Truncated-Type l k) →
    is-equiv (precomp f (type-Truncated-Type C))

  is-equiv-is-equiv-precomp-Truncated-Type :
    universal-property-equiv-Truncated-Type → is-equiv f
  is-equiv-is-equiv-precomp-Truncated-Type =
    is-equiv-is-equiv-precomp-structured-type (is-trunc k) A B f
```
