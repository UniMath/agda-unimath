# Localizations

```agda
module orthogonal-factorization-systems.localizations where
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
**localization** with respect to `P`, or **`P`-localization**, is a type `B` in
`P` and a map `η : A → B` such that every type in `P` is
`η`[-local](orthogonal-factorization-systems.local-types.md). I.e. for every `X`
in `P`, the precomposition map

```text
  _∘ η : (B → X) → (A → X)
```

is an equivalence.

## Definition

### The `is-localization` predicate on types

```agda
is-localization :
  {l lP : Level} (P : subuniverse l lP) → UU l → UU l → UU (lsuc l ⊔ lP)
is-localization {l} P A B =
  ( is-in-subuniverse P B) ×
  ( Σ ( A → B)
      ( λ η → (X : UU l) → is-in-subuniverse P X → is-local η X))
```

```agda
module _
  {l lP : Level} (P : subuniverse l lP) {A B : UU l}
  (is-localization-B : is-localization P A B)
  where

  is-in-subuniverse-is-localization : is-in-subuniverse P B
  is-in-subuniverse-is-localization = pr1 is-localization-B

  unit-is-localization : A → B
  unit-is-localization = pr1 (pr2 is-localization-B)

  is-local-at-unit-is-in-subuniverse-is-localization :
    (X : UU l) → is-in-subuniverse P X → is-local unit-is-localization X
  is-local-at-unit-is-in-subuniverse-is-localization =
    pr2 (pr2 is-localization-B)
```

### The type of localizations with respect to a subuniverse

```agda
localization :
  {l lP : Level} (P : subuniverse l lP) → UU l → UU (lsuc l ⊔ lP)
localization {l} P A = Σ (UU l) (is-localization P A)
```

```agda
module _
  {l lP : Level} (P : subuniverse l lP)
  {A : UU l} (L : localization P A)
  where

  type-localization : UU l
  type-localization = pr1 L

  is-localization-localization : is-localization P A type-localization
  is-localization-localization = pr2 L

  is-in-subuniverse-localization : is-in-subuniverse P type-localization
  is-in-subuniverse-localization =
    is-in-subuniverse-is-localization P is-localization-localization

  unit-localization : A → type-localization
  unit-localization = unit-is-localization P is-localization-localization

  is-local-at-unit-is-in-subuniverse-localization :
    (X : UU l) → is-in-subuniverse P X → is-local unit-localization X
  is-local-at-unit-is-in-subuniverse-localization =
    is-local-at-unit-is-in-subuniverse-is-localization
      P is-localization-localization
```

## Properties

### There is at most one `P`-localization of `A`

This is Proposition 5.1.2 in [Classifying Types](#classifying-types), and
remains to be formalized.

## References

1. Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
   theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
   ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
   [doi:10.23638](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
2. <a name="classifying-types"></a>Egbert Rijke, _Classifying Types_
   ([arXiv:1906.09435](https://arxiv.org/abs/1906.09435),
   [doi:10.48550](https://doi.org/10.48550/arXiv.1906.09435))
