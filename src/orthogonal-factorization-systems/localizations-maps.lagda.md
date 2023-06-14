# Localizations with respect to a map

```agda
module orthogonal-factorization-systems.localizations-maps where
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
open import orthogonal-factorization-systems.localizations-subuniverses
```

</details>

## Idea

Let `f` be a map of type `X → Y` and let `A` be a type. The **localization** of
`A` with respect to `f`, or **`f`-localization**, is a type `B` together with an
map `η : A → B` with the property that every type that is
`f`[-local](orthogonal-factorization-systems.local-types.md) is also `η`-local.

## Definition

### The predicate of being a localization with respect to a map

```agda
is-localization :
  {l1 l2 l3 l4 : Level} (l5 : Level)
  {X : UU l1} {Y : UU l2} (f : X → Y)
  (A : UU l3) (B : UU l4) (η : A → B) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5)
is-localization l5 f A B η =
  ( is-local f B) ×
  ( (W : UU l5) → is-local f W → is-local η W)
```

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {X : UU l1} {Y : UU l2} (f : X → Y)
  {A : UU l3} {B : UU l4} {η : A → B}
  (is-localization-B : is-localization l5 f A B η)
  where

  is-local-is-localization : is-local f B
  is-local-is-localization = pr1 is-localization-B
```

### The type of localizations of a type with respect to a map

```agda
localization :
  {l1 l2 l3 : Level} (l4 l5 : Level)
  {X : UU l1} {Y : UU l2} (f : X → Y)
  (A : UU l3) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4 ⊔ lsuc l5)
localization l4 l5 f A =
  Σ (UU l4) (λ B → Σ (A → B) (is-localization l5 f A B))
```

## Properties

### Localizations with respect to a map are localizations with respect to a subuniverse

```agda
module _
  {l1 l2 l3 l4 : Level}
  {X : UU l1} {Y : UU l2} (f : X → Y)
  (A : UU l3) (B : UU l4) (η : A → B)
  where

  is-subuniverse-localization-is-localization :
    is-localization l4 f A B η →
    is-subuniverse-localization (is-local-Prop f) A B
  pr1 (is-subuniverse-localization-is-localization is-localization-B) =
    pr1 is-localization-B
  pr1 (pr2 (is-subuniverse-localization-is-localization is-localization-B)) = η
  pr2 (pr2 (is-subuniverse-localization-is-localization is-localization-B))
    W is-local-W =
      pr2 is-localization-B W is-local-W
```

## References

1. Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
   theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
   ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
   [doi:10.23638](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
2. <a name="classifying-types"></a>Egbert Rijke, _Classifying Types_
   ([arXiv:1906.09435](https://arxiv.org/abs/1906.09435),
   [doi:10.48550](https://doi.org/10.48550/arXiv.1906.09435))
