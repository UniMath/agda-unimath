# Reflective subuniverses

```agda
module orthogonal-factorization-systems.reflective-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.subuniverses
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.localizations-subuniverses
open import orthogonal-factorization-systems.modal-induction
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.modal-subuniverse-induction
```

</details>

## Idea

A {{#concept "reflective subuniverse" Agda=reflective-subuniverse}} is a
[subuniverse](foundation.subuniverses.md) `P` together with a reflecting
operator `L : 𝒰 → 𝒰` that take values in `P`, and a
[unit](orthogonal-factorization-systems.modal-operators.md) `A → L A` for all
types `A` in `𝒰`, with the property that the types in `P` are
[local](orthogonal-factorization-systems.local-types.md) at the unit for every
`A`. Hence the local types with respect to `L` are precisely the types in the
reflective subuniverse.

## Definitions

### The predicate on subuniverses of being reflective

```agda
is-reflective-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU (lsuc l1 ⊔ l2)
is-reflective-subuniverse {l1} P =
  Σ ( operator-modality l1 l1)
    ( λ L →
      Σ ( unit-modality L)
        ( λ unit-L →
          ( (X : UU l1) → is-in-subuniverse P (L X)) ×
          ( (X Y : UU l1) → is-in-subuniverse P X → is-local (unit-L {Y}) X)))
```

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  (is-reflective-P : is-reflective-subuniverse P)
  where

  operator-is-reflective-subuniverse : operator-modality l1 l1
  operator-is-reflective-subuniverse = pr1 is-reflective-P

  unit-is-reflective-subuniverse :
    unit-modality (operator-is-reflective-subuniverse)
  unit-is-reflective-subuniverse = pr1 (pr2 is-reflective-P)

  is-in-subuniverse-operator-type-is-reflective-subuniverse :
    (X : UU l1) →
    is-in-subuniverse P (operator-is-reflective-subuniverse X)
  is-in-subuniverse-operator-type-is-reflective-subuniverse =
    pr1 (pr2 (pr2 is-reflective-P))

  is-local-is-in-subuniverse-is-reflective-subuniverse :
    (X Y : UU l1) →
    is-in-subuniverse P X →
    is-local (unit-is-reflective-subuniverse {Y}) X
  is-local-is-in-subuniverse-is-reflective-subuniverse =
    pr2 (pr2 (pr2 is-reflective-P))
```

### The type of reflective subuniverses

```agda
reflective-subuniverse : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
reflective-subuniverse l1 l2 =
  Σ (subuniverse l1 l2) (is-reflective-subuniverse)
```

```agda
module _
  {l1 l2 : Level} (P : reflective-subuniverse l1 l2)
  where

  subuniverse-reflective-subuniverse : subuniverse l1 l2
  subuniverse-reflective-subuniverse = pr1 P

  is-in-reflective-subuniverse : UU l1 → UU l2
  is-in-reflective-subuniverse =
    is-in-subuniverse subuniverse-reflective-subuniverse

  inclusion-reflective-subuniverse :
    type-subuniverse (subuniverse-reflective-subuniverse) → UU l1
  inclusion-reflective-subuniverse =
    inclusion-subuniverse subuniverse-reflective-subuniverse

  is-reflective-subuniverse-reflective-subuniverse :
    is-reflective-subuniverse (subuniverse-reflective-subuniverse)
  is-reflective-subuniverse-reflective-subuniverse = pr2 P

  operator-reflective-subuniverse : operator-modality l1 l1
  operator-reflective-subuniverse =
    operator-is-reflective-subuniverse
      ( subuniverse-reflective-subuniverse)
      ( is-reflective-subuniverse-reflective-subuniverse)

  unit-reflective-subuniverse :
    unit-modality (operator-reflective-subuniverse)
  unit-reflective-subuniverse =
    unit-is-reflective-subuniverse
      ( subuniverse-reflective-subuniverse)
      ( is-reflective-subuniverse-reflective-subuniverse)

  is-in-subuniverse-operator-type-reflective-subuniverse :
    ( X : UU l1) →
    is-in-subuniverse
      ( subuniverse-reflective-subuniverse)
      ( operator-reflective-subuniverse X)
  is-in-subuniverse-operator-type-reflective-subuniverse =
    is-in-subuniverse-operator-type-is-reflective-subuniverse
      ( subuniverse-reflective-subuniverse)
      ( is-reflective-subuniverse-reflective-subuniverse)

  is-local-is-in-subuniverse-reflective-subuniverse :
    ( X Y : UU l1) →
    is-in-subuniverse subuniverse-reflective-subuniverse X →
    is-local (unit-reflective-subuniverse {Y}) X
  is-local-is-in-subuniverse-reflective-subuniverse =
    is-local-is-in-subuniverse-is-reflective-subuniverse
      ( subuniverse-reflective-subuniverse)
      ( is-reflective-subuniverse-reflective-subuniverse)
```

## Properties

### Reflective subuniverses are subuniverses that have all localizations

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  (is-reflective-P : is-reflective-subuniverse P)
  where

  has-all-localizations-is-reflective-subuniverse :
    (A : UU l1) → subuniverse-localization P A
  pr1 (has-all-localizations-is-reflective-subuniverse A) =
    operator-is-reflective-subuniverse P is-reflective-P A
  pr1 (pr2 (has-all-localizations-is-reflective-subuniverse A)) =
    is-in-subuniverse-operator-type-is-reflective-subuniverse
      P is-reflective-P A
  pr1 (pr2 (pr2 (has-all-localizations-is-reflective-subuniverse A))) =
    unit-is-reflective-subuniverse P is-reflective-P
  pr2 (pr2 (pr2 (has-all-localizations-is-reflective-subuniverse A)))
    X is-in-subuniverse-X =
      is-local-is-in-subuniverse-is-reflective-subuniverse
        P is-reflective-P X A is-in-subuniverse-X

module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  (L : (A : UU l1) → subuniverse-localization P A)
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

## Recursion for reflective subuniverses

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  (is-reflective-P : is-reflective-subuniverse P)
  where

  rec-modality-is-reflective-subuniverse :
    rec-modality (unit-is-reflective-subuniverse P is-reflective-P)
  rec-modality-is-reflective-subuniverse {X} {Y} =
    map-inv-is-equiv
      ( is-local-is-in-subuniverse-is-reflective-subuniverse
        ( P)
        ( is-reflective-P)
        ( operator-is-reflective-subuniverse P is-reflective-P Y)
        ( X)
        ( is-in-subuniverse-operator-type-is-reflective-subuniverse
          ( P)
          ( is-reflective-P)
          ( Y)))

  map-is-reflective-subuniverse :
    {X Y : UU l1} → (X → Y) →
    operator-is-reflective-subuniverse P is-reflective-P X →
    operator-is-reflective-subuniverse P is-reflective-P Y
  map-is-reflective-subuniverse =
    ap-map-rec-modality
      ( unit-is-reflective-subuniverse P is-reflective-P)
      ( rec-modality-is-reflective-subuniverse)

  strong-rec-subuniverse-is-reflective-subuniverse :
    strong-rec-subuniverse-modality
      ( unit-is-reflective-subuniverse P is-reflective-P)
  strong-rec-subuniverse-is-reflective-subuniverse =
    strong-rec-subuniverse-rec-modality
      ( unit-is-reflective-subuniverse P is-reflective-P)
      ( rec-modality-is-reflective-subuniverse)

  rec-subuniverse-is-reflective-subuniverse :
    rec-subuniverse-modality (unit-is-reflective-subuniverse P is-reflective-P)
  rec-subuniverse-is-reflective-subuniverse =
    rec-subuniverse-rec-modality
      ( unit-is-reflective-subuniverse P is-reflective-P)
      ( rec-modality-is-reflective-subuniverse)
```

## See also

- [Σ-closed reflective subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.md)
- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.md)

## References

{{#bibliography}} {{#reference UF13}} {{#reference RSS20}} {{#reference Rij19}}
