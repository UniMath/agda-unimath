# Localizations at global subuniverses

```agda
module orthogonal-factorization-systems.localizations-at-global-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.cones-over-cospan-diagrams
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.extensions-types
open import foundation.extensions-types-global-subuniverses
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.global-subuniverses
open import foundation.homotopies
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.pullbacks
open import foundation.singleton-induction
open import foundation.subuniverses
open import foundation.unit-type
open import foundation.universe-levels

open import orthogonal-factorization-systems.orthogonal-maps
open import orthogonal-factorization-systems.pullback-hom
open import orthogonal-factorization-systems.types-local-at-maps
open import orthogonal-factorization-systems.universal-property-localizations-at-global-subuniverses
```

</details>

## Idea

Let `𝒫` be a [global subuniverse](foundation.global-subuniverses.md). Given a
type `X`, its
{{#concept "localization" Disambiguation="at a global subuniverse of types" Agda=is-localization-global-subuniverse}}
at `𝒫`, or **`𝒫`-localization**, is a type `LX` in `𝒫` and a map `η : X → LX`
such that every type in `𝒫` is
`η`[-local](orthogonal-factorization-systems.types-local-at-maps.md). I.e., for
every `Z` in `𝒫`, the [precomposition map](foundation-core.function-types.md)

```text
  - ∘ η : (LX → Z) → (X → Z)
```

is an [equivalence](foundation-core.equivalences.md).

## Definitions

### The type of localizations of a type at a global subuniverse

```agda
record
  localization-global-subuniverse
    {α : Level → Level} (𝒫 : global-subuniverse α)
    {l1 : Level} (l2 : Level) (X : UU l1) :
    UUω
  where

  constructor make-localization-global-subuniverse

  field
    reflection-localization-global-subuniverse :
      extension-type-global-subuniverse 𝒫 l2 X

  extension-type-localization-global-subuniverse :
    extension-type l2 X
  extension-type-localization-global-subuniverse =
    extension-type-extension-type-global-subuniverse 𝒫
      reflection-localization-global-subuniverse

  type-global-subuniverse-localization-global-subuniverse :
    type-global-subuniverse 𝒫 l2
  type-global-subuniverse-localization-global-subuniverse =
    type-global-subuniverse-extension-type-global-subuniverse 𝒫
      reflection-localization-global-subuniverse

  type-localization-global-subuniverse : UU l2
  type-localization-global-subuniverse =
    type-extension-type-global-subuniverse 𝒫
      reflection-localization-global-subuniverse

  is-in-global-subuniverse-type-localization-global-subuniverse :
    is-in-global-subuniverse 𝒫 type-localization-global-subuniverse
  is-in-global-subuniverse-type-localization-global-subuniverse =
    is-in-global-subuniverse-type-extension-type-global-subuniverse 𝒫
      reflection-localization-global-subuniverse

  unit-localization-global-subuniverse :
    X → type-localization-global-subuniverse
  unit-localization-global-subuniverse =
    inclusion-extension-type-global-subuniverse 𝒫
      reflection-localization-global-subuniverse

  field
    up-localization-global-subuniverse :
      universal-property-localization-global-subuniverse 𝒫 X
        reflection-localization-global-subuniverse

open localization-global-subuniverse public
```

## Properties

### Localizations are essentially unique

This is Proposition 5.1.2 in {{#cite Rij19}}.

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 l3 : Level} {X : UU l1}
  (LX : localization-global-subuniverse 𝒫 l2 X)
  (LX' : localization-global-subuniverse 𝒫 l3 X)
  where

  essentially-unique-type-localization-global-subuniverse :
    type-localization-global-subuniverse LX ≃
    type-localization-global-subuniverse LX'
  essentially-unique-type-localization-global-subuniverse =
    essentially-unique-type-universal-property-localization-global-subuniverse 𝒫
      ( reflection-localization-global-subuniverse LX)
      ( reflection-localization-global-subuniverse LX')
      ( up-localization-global-subuniverse LX)
      ( up-localization-global-subuniverse LX')

  essentially-unique-reflection-localization-global-subuniverse :
    equiv-extension-type-global-subuniverse 𝒫
      ( reflection-localization-global-subuniverse LX)
      ( reflection-localization-global-subuniverse LX')
  essentially-unique-reflection-localization-global-subuniverse =
    essentially-unique-extension-type-universal-property-localization-global-subuniverse
      ( 𝒫)
      ( reflection-localization-global-subuniverse LX)
      ( reflection-localization-global-subuniverse LX')
      ( up-localization-global-subuniverse LX)
      ( up-localization-global-subuniverse LX')
```

### Localizations are unique

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 : Level} {X : UU l1}
  (LX LX' : localization-global-subuniverse 𝒫 l2 X)
  where

  unique-type-localization-global-subuniverse :
    type-localization-global-subuniverse LX ＝
    type-localization-global-subuniverse LX'
  unique-type-localization-global-subuniverse =
    unique-type-universal-property-localization-global-subuniverse 𝒫
      ( reflection-localization-global-subuniverse LX)
      ( reflection-localization-global-subuniverse LX')
      ( up-localization-global-subuniverse LX)
      ( up-localization-global-subuniverse LX')

  unique-reflection-localization-global-subuniverse :
    reflection-localization-global-subuniverse LX ＝
    reflection-localization-global-subuniverse LX'
  unique-reflection-localization-global-subuniverse =
    unique-extension-type-universal-property-localization-global-subuniverse 𝒫
      ( reflection-localization-global-subuniverse LX)
      ( reflection-localization-global-subuniverse LX')
      ( up-localization-global-subuniverse LX)
      ( up-localization-global-subuniverse LX')
```

### If the unit type has a `𝒫`-localization then it is in `𝒫`

This is Corollary 5.1.4 of {{#cite Rij19}}.

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  where

  is-equiv-unit-has-localization-global-subuniverse-unit :
    {l : Level} (L : localization-global-subuniverse 𝒫 l unit) →
    is-equiv (unit-localization-global-subuniverse L)
  is-equiv-unit-has-localization-global-subuniverse-unit L =
    is-equiv-unit-retraction-universal-property-localization-global-subuniverse
      ( 𝒫)
      ( reflection-localization-global-subuniverse L)
      ( up-localization-global-subuniverse L)
      ( retraction-point (unit-localization-global-subuniverse L star))

  is-in-global-subuniverse-has-localization-global-subuniverse-unit :
    {l : Level} (L : localization-global-subuniverse 𝒫 l unit) →
    is-in-global-subuniverse 𝒫 unit
  is-in-global-subuniverse-has-localization-global-subuniverse-unit L =
    is-in-global-subuniverse-is-equiv-unit-universal-property-localization-global-subuniverse
      ( 𝒫)
      ( reflection-localization-global-subuniverse L)
      ( up-localization-global-subuniverse L)
      ( is-equiv-unit-has-localization-global-subuniverse-unit L)
```

### If a contractible type has a `𝒫`-localization then it is in `𝒫`

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 : Level} {A : UU l1} (H : is-contr A)
  (LA : localization-global-subuniverse 𝒫 l2 A)
  where

  is-equiv-unit-has-localization-global-subuniverse-is-contr :
    is-equiv (unit-localization-global-subuniverse LA)
  is-equiv-unit-has-localization-global-subuniverse-is-contr =
    is-equiv-unit-retraction-universal-property-localization-global-subuniverse
      ( 𝒫)
      ( reflection-localization-global-subuniverse LA)
      ( up-localization-global-subuniverse LA)
      ( const (type-localization-global-subuniverse LA) (center H) ,
        contraction H)

  is-in-global-subuniverse-has-localization-global-subuniverse-is-contr :
    is-in-global-subuniverse 𝒫 A
  is-in-global-subuniverse-has-localization-global-subuniverse-is-contr =
    is-in-global-subuniverse-is-equiv-unit-universal-property-localization-global-subuniverse
      ( 𝒫)
      ( reflection-localization-global-subuniverse LA)
      ( up-localization-global-subuniverse LA)
      ( is-equiv-unit-has-localization-global-subuniverse-is-contr)
```

### Dependent sums of dependent types over localizations

Given a localization `η : X → LX` with respect to a global subuniverse `𝒫` and a
dependent type `P` over `LX`, then if the dependent sum `Σ (l : LX), P l` is in
`𝒫` the dependent type `P` is `η`-local.

This is stated as Proposition 5.1.5 in {{#cite Rij19}} and as Proposition 2.8 in
{{#cite CORS20}}.

**Proof.** Consider the following diagram.

```text
                          - ∘ η
      (Π (l : LX), P l) --------> (Π (x : X), P (η x))
             |                             |
             |                             |
             |                             |
             |                             |
             ∨            - ∘ η            ∨
  (LX → Σ (l : LX), P l) ------> (X → Σ (l : LX), P l)
             |                             |
             |                             |
     pr1 ∘ - |                             | pr1 ∘ -
             |                             |
             ∨            - ∘ η            ∨
    id ∈ (LX → LX) -------------------> (X → LX)
```

The bottom horizontal map is an equivalence by the universal property of the
localization and the top vertical maps are fiber inclusions. Therefore, the
middle horizontal map is an equivalence and the bottom square is a pullback if
and only if the the top horizontal map is an equivalence.

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 l3 : Level} {X : UU l1}
  (LX : localization-global-subuniverse 𝒫 l2 X)
  {P : type-localization-global-subuniverse LX → UU l3}
  where

  is-local-dependent-type-is-in-global-subuniverse-Σ-localization-global-subuniverse :
    is-in-global-subuniverse 𝒫 (Σ (type-localization-global-subuniverse LX) P) →
    is-local-dependent-type (unit-localization-global-subuniverse LX) P
  is-local-dependent-type-is-in-global-subuniverse-Σ-localization-global-subuniverse
    H =
    is-equiv-target-is-equiv-source-equiv-arrow _ _
      ( equiv-Π-equiv-family (equiv-fiber-pr1 P) ,
        equiv-Π-equiv-family
          ( equiv-fiber-pr1 P ∘ unit-localization-global-subuniverse LX) ,
        refl-htpy)
      ( is-orthogonal-fiber-condition-right-map-is-orthogonal-pullback-condition
        ( unit-localization-global-subuniverse LX)
        ( pr1 {B = P})
        ( is-pullback-is-equiv-horizontal-maps _ _
          ( cone-pullback-hom (unit-localization-global-subuniverse LX) pr1)
          ( up-localization-global-subuniverse LX
            ( type-global-subuniverse-localization-global-subuniverse LX))
          ( up-localization-global-subuniverse LX
            ( Σ (type-localization-global-subuniverse LX) P , H)))
        ( id))
```

> This formalized proof can be made more elegant by formalizing the concept of
> type families that are orthogonal to maps.

## See also

- [Localizations at maps](orthogonal-factorization-systems.localizations-at-maps.md)

## References

{{#bibliography}} {{#reference Rij19}}
