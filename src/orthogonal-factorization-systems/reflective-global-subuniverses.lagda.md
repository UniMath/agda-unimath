# Reflective global subuniverses

```agda
module orthogonal-factorization-systems.reflective-global-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.extensions-types-global-subuniverses
open import foundation.extensions-types-subuniverses
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.global-subuniverses
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.subuniverses
open import foundation.unit-type
open import foundation.universe-levels

open import orthogonal-factorization-systems.localizations-at-global-subuniverses
open import orthogonal-factorization-systems.modal-induction
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.modal-subuniverse-induction
open import orthogonal-factorization-systems.types-local-at-maps
open import orthogonal-factorization-systems.universal-property-localizations-at-global-subuniverses
open import orthogonal-factorization-systems.universal-property-localizations-at-subuniverses
```

</details>

## Idea

A
{{#concept "reflective global subuniverse" Disambiguation="of types" Agda=reflective-global-subuniverse}},
or
{{#concept "localization" Disambiguation="subuniverse" Agda=reflective-global-subuniverse}},
is a [global subuniverse](foundation.global-subuniverses.md) `𝒫` together with a
reflecting operator on types `L` that takes values in `𝒫`, and a family of unit
maps `η : A → LA` for all types `A`, with the property that the types in `𝒫` are
[local](orthogonal-factorization-systems.types-local-at-maps.md) at the unit for
every `A`. Hence the local types with respect to `L` are precisely the types in
the reflective global subuniverse.

## Definitions

### The predicate on global subuniverses of being reflective

```agda
is-reflective-global-subuniverse :
    {α : Level → Level} → (Level → Level) → global-subuniverse α → UUω
is-reflective-global-subuniverse β 𝒫 =
  {l : Level} (X : UU l) → localization-global-subuniverse 𝒫 (β l) X

module _
  {α β : Level → Level}
  (𝒫 : global-subuniverse α)
  (H : is-reflective-global-subuniverse β 𝒫)
  where

  reflection-is-reflective-global-subuniverse :
    {l : Level} (X : UU l) → extension-type-global-subuniverse 𝒫 (β l) X
  reflection-is-reflective-global-subuniverse X =
    reflection-localization-global-subuniverse (H X)

  type-reflection-is-reflective-global-subuniverse :
    {l : Level} → UU l → UU (β l)
  type-reflection-is-reflective-global-subuniverse X =
    type-localization-global-subuniverse (H X)

  is-in-global-subuniverse-type-reflection-is-reflective-global-subuniverse :
    {l : Level} (X : UU l) →
    is-in-global-subuniverse 𝒫
      ( type-reflection-is-reflective-global-subuniverse X)
  is-in-global-subuniverse-type-reflection-is-reflective-global-subuniverse X =
    is-in-global-subuniverse-type-localization-global-subuniverse (H X)

  unit-is-reflective-global-subuniverse :
    {l : Level} (X : UU l) →
    X → type-reflection-is-reflective-global-subuniverse X
  unit-is-reflective-global-subuniverse X =
    unit-localization-global-subuniverse (H X)

  up-localization-is-reflective-global-subuniverse :
    {l : Level} (X : UU l) →
    universal-property-localization-global-subuniverse 𝒫 X
      ( reflection-is-reflective-global-subuniverse X)
  up-localization-is-reflective-global-subuniverse X =
    up-localization-global-subuniverse (H X)
```

### Reflective global subuniverses

```agda
record
  reflective-global-subuniverse (α β : Level → Level) : UUω
  where

  field
    global-subuniverse-reflective-global-subuniverse :
      global-subuniverse α

    is-reflective-reflective-global-subuniverse :
      is-reflective-global-subuniverse β
        global-subuniverse-reflective-global-subuniverse
```

```agda
  subuniverse-reflective-global-subuniverse : (l : Level) → subuniverse l (α l)
  subuniverse-reflective-global-subuniverse =
    subuniverse-global-subuniverse
      global-subuniverse-reflective-global-subuniverse

  is-closed-under-equiv-reflective-global-subuniverse :
    {l1 l2 : Level} →
    is-closed-under-equiv-subuniverses α
      subuniverse-reflective-global-subuniverse
      l1
      l2
  is-closed-under-equiv-reflective-global-subuniverse =
    is-closed-under-equiv-global-subuniverse
      global-subuniverse-reflective-global-subuniverse

  is-in-reflective-global-subuniverse : {l : Level} → UU l → UU (α l)
  is-in-reflective-global-subuniverse =
    is-in-global-subuniverse global-subuniverse-reflective-global-subuniverse

  is-prop-is-in-reflective-global-subuniverse :
    {l : Level} (X : UU l) → is-prop (is-in-reflective-global-subuniverse X)
  is-prop-is-in-reflective-global-subuniverse =
    is-prop-is-in-global-subuniverse
      global-subuniverse-reflective-global-subuniverse

  type-reflective-global-subuniverse : (l : Level) → UU (α l ⊔ lsuc l)
  type-reflective-global-subuniverse =
    type-global-subuniverse
      global-subuniverse-reflective-global-subuniverse

  inclusion-reflective-global-subuniverse :
    {l : Level} → type-reflective-global-subuniverse l → UU l
  inclusion-reflective-global-subuniverse =
    inclusion-global-subuniverse
      global-subuniverse-reflective-global-subuniverse

  type-reflection-reflective-global-subuniverse :
    {l : Level} → UU l → UU (β l)
  type-reflection-reflective-global-subuniverse =
    type-reflection-is-reflective-global-subuniverse
      global-subuniverse-reflective-global-subuniverse
      is-reflective-reflective-global-subuniverse

  is-in-global-subuniverse-type-reflection-reflective-global-subuniverse :
    {l : Level} (X : UU l) →
    is-in-reflective-global-subuniverse
      ( type-reflection-reflective-global-subuniverse X)
  is-in-global-subuniverse-type-reflection-reflective-global-subuniverse =
    is-in-global-subuniverse-type-reflection-is-reflective-global-subuniverse
      global-subuniverse-reflective-global-subuniverse
      is-reflective-reflective-global-subuniverse

  reflection-reflective-global-subuniverse :
      {l : Level} (X : UU l) →
      extension-type-global-subuniverse
        global-subuniverse-reflective-global-subuniverse
        ( β l)
        ( X)
  reflection-reflective-global-subuniverse =
    reflection-is-reflective-global-subuniverse
      global-subuniverse-reflective-global-subuniverse
      is-reflective-reflective-global-subuniverse

  unit-reflective-global-subuniverse :
    {l : Level} (X : UU l) →
    X → type-reflection-reflective-global-subuniverse X
  unit-reflective-global-subuniverse =
    unit-is-reflective-global-subuniverse
      global-subuniverse-reflective-global-subuniverse
      is-reflective-reflective-global-subuniverse

  up-localization-reflective-global-subuniverse :
    {l : Level} (X : UU l) →
    universal-property-localization-global-subuniverse
      global-subuniverse-reflective-global-subuniverse
      ( X)
      ( reflection-reflective-global-subuniverse X)
  up-localization-reflective-global-subuniverse =
    up-localization-is-reflective-global-subuniverse
      global-subuniverse-reflective-global-subuniverse
      is-reflective-reflective-global-subuniverse

open reflective-global-subuniverse public
```

## Properties

### A type is in a reflective subuniverse if and only if it is local at reflections

```agda
module _
  {α β : Level → Level}
  (𝒫 : reflective-global-subuniverse α β)
  where

  is-in-reflective-global-subuniverse-is-local-domain :
    {l1 : Level} {A : UU l1} →
    is-local (unit-reflective-global-subuniverse 𝒫 A) A →
    is-in-reflective-global-subuniverse 𝒫 A
  is-in-reflective-global-subuniverse-is-local-domain {A = A} =
    is-in-global-subuniverse-is-local-type-universal-property-localization-global-subuniverse
      ( global-subuniverse-reflective-global-subuniverse 𝒫)
      ( reflection-reflective-global-subuniverse 𝒫 A)
      ( up-localization-reflective-global-subuniverse 𝒫 A)

  is-in-reflective-global-subuniverse-is-local :
    {l1 : Level} {A : UU l1} →
    ( {l : Level} (X : UU l) →
      is-local (unit-reflective-global-subuniverse 𝒫 X) A) →
    is-in-reflective-global-subuniverse 𝒫 A
  is-in-reflective-global-subuniverse-is-local {A = A} H =
    is-in-reflective-global-subuniverse-is-local-domain (H A)
```

### A type `X` is in a reflective subuniverse if and only if the unit is an equivalence at `X`

```agda
module _
  {α β : Level → Level}
  (𝒫 : reflective-global-subuniverse α β)
  {l : Level} {X : UU l}
  where

  is-in-reflective-global-subuniverse-is-equiv-unit :
    is-equiv (unit-reflective-global-subuniverse 𝒫 X) →
    is-in-reflective-global-subuniverse 𝒫 X
  is-in-reflective-global-subuniverse-is-equiv-unit =
    is-in-global-subuniverse-is-equiv-unit-universal-property-localization-global-subuniverse
      ( global-subuniverse-reflective-global-subuniverse 𝒫)
      ( reflection-reflective-global-subuniverse 𝒫 X)
      ( up-localization-reflective-global-subuniverse 𝒫 X)

  is-equiv-unit-is-in-reflective-global-subuniverse :
    is-in-reflective-global-subuniverse 𝒫 X →
    is-equiv (unit-reflective-global-subuniverse 𝒫 X)
  is-equiv-unit-is-in-reflective-global-subuniverse =
    is-equiv-unit-is-in-global-subuniverse-universal-property-localization-global-subuniverse
      ( global-subuniverse-reflective-global-subuniverse 𝒫)
      ( reflection-reflective-global-subuniverse 𝒫 X)
      ( up-localization-reflective-global-subuniverse 𝒫 X)
```

### Reflective global subuniverses contain contractible types

```agda
module _
  {α β : Level → Level} (𝒫 : reflective-global-subuniverse α β)
  where

  is-in-reflective-global-subuniverse-unit :
    is-in-reflective-global-subuniverse 𝒫 unit
  is-in-reflective-global-subuniverse-unit =
    is-in-global-subuniverse-has-localization-global-subuniverse-unit
      ( global-subuniverse-reflective-global-subuniverse 𝒫)
      ( is-reflective-reflective-global-subuniverse 𝒫 unit)

  is-in-reflective-global-subuniverse-is-contr :
    {l : Level} {A : UU l} →
    is-contr A →
    is-in-reflective-global-subuniverse 𝒫 A
  is-in-reflective-global-subuniverse-is-contr {A = A} H =
    is-in-global-subuniverse-has-localization-global-subuniverse-is-contr
      ( global-subuniverse-reflective-global-subuniverse 𝒫)
      ( H)
      ( is-reflective-reflective-global-subuniverse 𝒫 A)
```

### Reflective global subuniverses are closed under pullbacks

### Reflective global subuniverses are closed under identity types

### Reflective global subuniverses are closed under sequential limits

## See also

- [Σ-closed reflective subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.md)
- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-at-subuniverses.md)

## References

{{#bibliography}} {{#reference UF13}} {{#reference RSS20}} {{#reference Rij19}}
