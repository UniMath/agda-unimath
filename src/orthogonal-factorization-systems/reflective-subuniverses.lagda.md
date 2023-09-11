# Reflective subuniverses

```agda
module orthogonal-factorization-systems.reflective-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.subuniverses
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.localizations-subuniverses
open import orthogonal-factorization-systems.modal-operators
```

</details>

## Idea

A **reflective subuniverse** is a [subuniverse](foundation.subuniverses.md) `P`
together with a reflecting operator `○ : UU → UU` that take values in `P`, and a
[modal unit](orthogonal-factorization-systems.modal-operators.md) `A → ○ A` for
all [small types](foundation-core.small-types.md) `A`, with the property that
the types in `P` are [local](orthogonal-factorization-systems.local-types.md) at
the modal unit for every `A`. Hence the modal types with respect to `○` are
precisely the types in the reflective subuniverse.

## Definitions

### The `is-reflective-subuniverse` predicate on subuniverses

```agda
is-reflective-subuniverse :
  {l lP : Level} (P : UU l → Prop lP) → UU (lsuc l ⊔ lP)
is-reflective-subuniverse {l} P =
  Σ ( operator-modality l l)
    ( λ ○ →
      Σ ( unit-modality ○)
        ( λ unit-○ →
          ( (X : UU l) → is-in-subuniverse P (○ X)) ×
          ( (X Y : UU l) → is-in-subuniverse P X → is-local (unit-○ {Y}) X)))
```

```agda
module _
  {l lP : Level} (P : subuniverse l lP)
  (is-reflective-P : is-reflective-subuniverse P)
  where

  operator-modality-is-reflective-subuniverse : operator-modality l l
  operator-modality-is-reflective-subuniverse = pr1 is-reflective-P

  unit-modality-is-reflective-subuniverse :
    unit-modality (operator-modality-is-reflective-subuniverse)
  unit-modality-is-reflective-subuniverse = pr1 (pr2 is-reflective-P)

  is-in-subuniverse-image-operator-modality-is-reflective-subuniverse :
    (X : UU l) →
    is-in-subuniverse P (operator-modality-is-reflective-subuniverse X)
  is-in-subuniverse-image-operator-modality-is-reflective-subuniverse =
    pr1 (pr2 (pr2 is-reflective-P))

  is-local-is-in-subuniverse-is-reflective-subuniverse :
    (X Y : UU l) →
    is-in-subuniverse P X →
    is-local (unit-modality-is-reflective-subuniverse {Y}) X
  is-local-is-in-subuniverse-is-reflective-subuniverse =
    pr2 (pr2 (pr2 is-reflective-P))
```

### The type of reflective subuniverses

```agda
reflective-subuniverse : (l lP : Level) → UU (lsuc l ⊔ lsuc lP)
reflective-subuniverse l lP =
  Σ (UU l → Prop lP) (is-reflective-subuniverse)
```

```agda
module _
  {l lP : Level} (P : reflective-subuniverse l lP)
  where

  subuniverse-reflective-subuniverse : subuniverse l lP
  subuniverse-reflective-subuniverse = pr1 P

  is-in-reflective-subuniverse : UU l → UU lP
  is-in-reflective-subuniverse =
    is-in-subuniverse subuniverse-reflective-subuniverse

  inclusion-reflective-subuniverse :
    type-subuniverse (subuniverse-reflective-subuniverse) → UU l
  inclusion-reflective-subuniverse =
    inclusion-subuniverse subuniverse-reflective-subuniverse

  is-reflective-subuniverse-reflective-subuniverse :
    is-reflective-subuniverse (subuniverse-reflective-subuniverse)
  is-reflective-subuniverse-reflective-subuniverse = pr2 P

  operator-modality-reflective-subuniverse : operator-modality l l
  operator-modality-reflective-subuniverse =
    operator-modality-is-reflective-subuniverse
      ( subuniverse-reflective-subuniverse)
      ( is-reflective-subuniverse-reflective-subuniverse)

  unit-modality-reflective-subuniverse :
    unit-modality (operator-modality-reflective-subuniverse)
  unit-modality-reflective-subuniverse =
    unit-modality-is-reflective-subuniverse
      ( subuniverse-reflective-subuniverse)
      ( is-reflective-subuniverse-reflective-subuniverse)

  is-in-subuniverse-image-operator-modality-reflective-subuniverse :
    ( X : UU l) →
    is-in-subuniverse
      ( subuniverse-reflective-subuniverse)
      ( operator-modality-reflective-subuniverse X)
  is-in-subuniverse-image-operator-modality-reflective-subuniverse =
    is-in-subuniverse-image-operator-modality-is-reflective-subuniverse
      ( subuniverse-reflective-subuniverse)
      ( is-reflective-subuniverse-reflective-subuniverse)

  is-local-is-in-subuniverse-reflective-subuniverse :
    ( X Y : UU l) →
    is-in-subuniverse subuniverse-reflective-subuniverse X →
    is-local (unit-modality-reflective-subuniverse {Y}) X
  is-local-is-in-subuniverse-reflective-subuniverse =
    is-local-is-in-subuniverse-is-reflective-subuniverse
      ( subuniverse-reflective-subuniverse)
      ( is-reflective-subuniverse-reflective-subuniverse)
```

## Properties

### Reflective subuniverses are subuniverses that have all localizations

```agda
module _
  {l lP : Level} (P : subuniverse l lP)
  (is-reflective-P : is-reflective-subuniverse P)
  where

  has-all-localizations-is-reflective-subuniverse :
    (A : UU l) → subuniverse-localization P A
  pr1 (has-all-localizations-is-reflective-subuniverse A) =
    operator-modality-is-reflective-subuniverse P is-reflective-P A
  pr1 (pr2 (has-all-localizations-is-reflective-subuniverse A)) =
    is-in-subuniverse-image-operator-modality-is-reflective-subuniverse
      P is-reflective-P A
  pr1 (pr2 (pr2 (has-all-localizations-is-reflective-subuniverse A))) =
    unit-modality-is-reflective-subuniverse P is-reflective-P
  pr2 (pr2 (pr2 (has-all-localizations-is-reflective-subuniverse A)))
    X is-in-subuniverse-X =
      is-local-is-in-subuniverse-is-reflective-subuniverse
        P is-reflective-P X A is-in-subuniverse-X

module _
  {l lP : Level} (P : subuniverse l lP)
  (L : (A : UU l) → subuniverse-localization P A)
  where

  is-reflective-has-all-localizations-subuniverse :
    is-reflective-subuniverse P
  pr1 is-reflective-has-all-localizations-subuniverse A =
    type-subuniverse-localization P (L A)
  pr1 (pr2 is-reflective-has-all-localizations-subuniverse) {A} =
    unit-subuniverse-localization P (L A)
  pr1 (pr2 (pr2 is-reflective-has-all-localizations-subuniverse)) A =
    is-in-subuniverse-subuniverse-localization P (L A)
  pr2 (pr2 (pr2 is-reflective-has-all-localizations-subuniverse))
    A B is-in-subuniverse-A =
      is-local-at-unit-is-in-subuniverse-subuniverse-localization
        P (L B) A is-in-subuniverse-A
```

## See also

- [Σ-closed reflective subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.md)
- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.md)

## References

1. Univalent Foundations Project, _Homotopy Type Theory – Univalent Foundations
   of Mathematics_ (2013) ([website](https://homotopytypetheory.org/book/),
   [arXiv:1308.0729](https://arxiv.org/abs/1308.0729),
   [DOI:10.48550](https://doi.org/10.48550/arXiv.1308.0729))
2. Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
   theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
   ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
   [doi:10.23638](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
3. Egbert Rijke, _Classifying Types_
   ([arXiv:1906.09435](https://arxiv.org/abs/1906.09435),
   [doi:10.48550](https://doi.org/10.48550/arXiv.1906.09435))
