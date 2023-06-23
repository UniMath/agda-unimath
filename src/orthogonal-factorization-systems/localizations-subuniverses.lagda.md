# Localizations at a subuniverse

```agda
module orthogonal-factorization-systems.localizations-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.subuniverses
open import foundation.type-arithmetic-dependent-function-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-empty-type
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
```

</details>

## Idea

Let `P` be a [subuniverse](foundation.subuniverses.md). Given a type `A`, its
**localization** at `P`, or **`P`-localization**, is a type `B` in `P` and a map
`η : A → B` such that every type in `P` is
`η`[-local](orthogonal-factorization-systems.local-types.md). I.e. for every `X`
in `P`, the precomposition map

```text
  _∘ η : (B → X) → (A → X)
```

is an equivalence.

## Definition

### The predicate of being a localization at a subuniverse

```agda
is-subuniverse-localization :
  {l1 l2 lP : Level} (P : subuniverse l1 lP) →
  UU l2 → UU l1 → UU (lsuc l1 ⊔ l2 ⊔ lP)
is-subuniverse-localization {l1} {l2} P A B =
  ( is-in-subuniverse P B) ×
  ( Σ ( A → B)
      ( λ η → (X : UU l1) → is-in-subuniverse P X → is-local η X))
```

```agda
module _
  {l1 l2 lP : Level} (P : subuniverse l1 lP) {A : UU l2} {B : UU l1}
  (is-localization-B : is-subuniverse-localization P A B)
  where

  is-in-subuniverse-is-subuniverse-localization : is-in-subuniverse P B
  is-in-subuniverse-is-subuniverse-localization = pr1 is-localization-B

  unit-is-subuniverse-localization : A → B
  unit-is-subuniverse-localization = pr1 (pr2 is-localization-B)

  is-local-at-unit-is-in-subuniverse-is-subuniverse-localization :
    (X : UU l1) → is-in-subuniverse P X →
    is-local unit-is-subuniverse-localization X
  is-local-at-unit-is-in-subuniverse-is-subuniverse-localization =
    pr2 (pr2 is-localization-B)
```

### The type of localizations at a subuniverse

```agda
subuniverse-localization :
  {l1 l2 lP : Level} (P : subuniverse l1 lP) → UU l2 → UU (lsuc l1 ⊔ l2 ⊔ lP)
subuniverse-localization {l1} P A = Σ (UU l1) (is-subuniverse-localization P A)
```

```agda
module _
  {l1 l2 lP : Level} (P : subuniverse l1 lP)
  {A : UU l2} (L : subuniverse-localization P A)
  where

  type-subuniverse-localization : UU l1
  type-subuniverse-localization = pr1 L

  is-subuniverse-localization-subuniverse-localization :
    is-subuniverse-localization P A type-subuniverse-localization
  is-subuniverse-localization-subuniverse-localization = pr2 L

  is-in-subuniverse-subuniverse-localization :
    is-in-subuniverse P type-subuniverse-localization
  is-in-subuniverse-subuniverse-localization =
    is-in-subuniverse-is-subuniverse-localization P
      ( is-subuniverse-localization-subuniverse-localization)

  unit-subuniverse-localization : A → type-subuniverse-localization
  unit-subuniverse-localization =
    unit-is-subuniverse-localization P
      ( is-subuniverse-localization-subuniverse-localization)

  is-local-at-unit-is-in-subuniverse-subuniverse-localization :
    (X : UU l1) →
    is-in-subuniverse P X → is-local unit-subuniverse-localization X
  is-local-at-unit-is-in-subuniverse-subuniverse-localization =
    is-local-at-unit-is-in-subuniverse-is-subuniverse-localization P
      ( is-subuniverse-localization-subuniverse-localization)
```

## Properties

### There is at most one `P`-localization of `A`

This is Proposition 5.1.2 in _Classifying Types_, and remains to be formalized.

## References

1. Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
   theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
   ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
   [doi:10.23638](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
2. <a name="classifying-types"></a>Egbert Rijke, _Classifying Types_
   ([arXiv:1906.09435](https://arxiv.org/abs/1906.09435),
   [doi:10.48550](https://doi.org/10.48550/arXiv.1906.09435))
