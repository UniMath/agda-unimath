# Localizations at global subuniverses

```agda
module orthogonal-factorization-systems.localizations-at-global-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.cones-over-cospan-diagrams
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.extensions-types
open import foundation.extensions-types-global-subuniverses
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.global-subuniverses
open import foundation.homotopies
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.pullback-cones
open import foundation.pullbacks
open import foundation.sequential-limits
open import foundation.singleton-induction
open import foundation.subuniverses
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import orthogonal-factorization-systems.orthogonal-maps
open import orthogonal-factorization-systems.pullback-hom
open import orthogonal-factorization-systems.types-local-at-maps
open import orthogonal-factorization-systems.universal-property-localizations-at-global-subuniverses
```

</details>

## Idea

Let `𝒫` be a [global subuniverse](foundation.global-subuniverses.md). Given a
type `X`, its
{{#concept "localization" Disambiguation="at a global subuniverse of types" Agda=localization-global-subuniverse}}
at `𝒫`, or **`𝒫`-localization**, is a type `LX` in `𝒫` and a map `η : X → LX`
such that every type in `𝒫` is
`η`-[local](orthogonal-factorization-systems.types-local-at-maps.md). I.e., for
every `Z` in `𝒫`, the [precomposition map](foundation-core.function-types.md)

```text
  - ∘ η : (LX → Z) → (X → Z)
```

is an [equivalence](foundation-core.equivalences.md). This is referred to as the
[universal property of localizations](orthogonal-factorization-systems.universal-property-localizations-at-global-subuniverses.md).

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
and only if the top horizontal map is an equivalence.

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

**Alternative proof.** We have an equivalence of arrows

```text
                                precomp η (Σ LX P)
             (B → Σ LX P) ------------------------------> (A → Σ LX P)
                  |                                           |
                ~ |                                           | ~
                  ∨                                           ∨
  Σ (h : B → LX) ((y : B) → P (h y)) --------> Σ (h : A → LX) ((x : A) → P (h x)).
                  map-Σ _ (precomp η LX) (λ h → precomp-Π η (P ∘ h))
```

and the functoriality of dependent pair types decomposes as a composite

```text
  map-Σ _ (precomp η LX) (λ h → precomp-Π η (P ∘ h)) ~
  map-Σ-map-base _ (precomp η LX) ∘ tot (λ h → precomp-Π η (P ∘ h)).
```

Since `LX` is `𝒫`-local the map `map-Σ-map-base _ (precomp η LX)` is an
equivalence. Therefore, `precomp η (Σ LX P)` is an equivalence if and only if
`λ h → precomp-Π η (P ∘ h)` is a fiberwise equivalence. In particular, if
`precomp η (Σ LX P)` is an equivalence then `precomp-Π η P` is an equivalence.

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 l3 : Level} {X : UU l1}
  (LX : localization-global-subuniverse 𝒫 l2 X)
  {P : type-localization-global-subuniverse LX → UU l3}
  where

  is-local-dependent-type-is-in-global-subuniverse-Σ-localization-global-subuniverse' :
    is-in-global-subuniverse 𝒫 (Σ (type-localization-global-subuniverse LX) P) →
    is-local-dependent-type (unit-localization-global-subuniverse LX) P
  is-local-dependent-type-is-in-global-subuniverse-Σ-localization-global-subuniverse'
    H =
    is-fiberwise-equiv-is-equiv-map-Σ
      ( λ h → (x : X) → P (h x))
      ( precomp
        ( unit-localization-global-subuniverse LX)
        ( type-localization-global-subuniverse LX))
      ( λ h → precomp-Π (unit-localization-global-subuniverse LX) (P ∘ h))
      ( up-localization-global-subuniverse LX
        ( type-global-subuniverse-localization-global-subuniverse LX))
      ( is-equiv-target-is-equiv-source-equiv-arrow
        ( precomp
          ( unit-localization-global-subuniverse LX)
          ( Σ (type-localization-global-subuniverse LX) P))
        ( map-Σ
          ( λ h → (x : X) → P (h x))
          ( precomp
            ( unit-localization-global-subuniverse LX)
            ( type-localization-global-subuniverse LX))
          ( λ h → precomp-Π (unit-localization-global-subuniverse LX) (P ∘ h)))
        ( distributive-Π-Σ , distributive-Π-Σ , coherence-precomp-Σ)
        ( up-localization-global-subuniverse LX
          ( Σ (type-localization-global-subuniverse LX) P , H)))
      ( id)
```

### Dependent products of `𝒫`-types that have a `𝒫`-localization are `𝒫`-types

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (K : (x : A) → is-in-global-subuniverse 𝒫 (B x))
  (LE : localization-global-subuniverse 𝒫 l3 ((x : A) → B x))
  where

  is-in-global-subuniverse-Π-localization-global-subuniverse :
    is-in-global-subuniverse 𝒫 ((x : A) → B x)
  is-in-global-subuniverse-Π-localization-global-subuniverse =
    is-in-global-subuniverse-is-local-type-universal-property-localization-global-subuniverse
      ( 𝒫)
      ( reflection-localization-global-subuniverse LE)
      ( up-localization-global-subuniverse LE)
      ( distributive-Π-is-local
        ( unit-localization-global-subuniverse LE)
        ( B)
        ( λ x → up-localization-global-subuniverse LE (B x , K x)))
```

### Exponentials of `𝒫`-types that have a `𝒫`-localization are `𝒫`-types

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (K : is-in-global-subuniverse 𝒫 B)
  (LE : localization-global-subuniverse 𝒫 l3 (A → B))
  where

  is-in-global-subuniverse-exponential-localization-global-subuniverse :
    is-in-global-subuniverse 𝒫 (A → B)
  is-in-global-subuniverse-exponential-localization-global-subuniverse =
    is-in-global-subuniverse-Π-localization-global-subuniverse 𝒫 (λ _ → K) LE
```

### Localizations of types of homotopies

Assume given a `𝒫`-localization `η : X → LX` and two maps `f g : LX → Y` where
`Y ∈ 𝒫`, then the right whiskering map `- ·r η : (g ~ h) → (g ∘ η ~ h ∘ η)` is
an equivalence.

This is Lemma 5.1.18 in {{#cite Rij19}}.

**Proof.** We have an equivalence of maps

```text
                ap (- ∘ η)
        g ＝ h -----------> g ∘ η ＝ h ∘ η
          |                       |
  htpy-eq | ~                   ~ | htpy-eq
          ∨                       ∨
        g ~ h ------------> g ∘ η ~ h ∘ η
                  - ·r η
```

and the map `- ∘ η` is an embedding since `Y` is `η`-local by the universal
property, hence the top horizontal map is an equivalence and so the bottom map
is as well.

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l3}
  (LX : localization-global-subuniverse 𝒫 l2 X)
  (H : is-in-global-subuniverse 𝒫 Y)
  where

  is-equiv-right-whisker-unit-localization-global-subuniverse :
    {g h : type-localization-global-subuniverse LX → Y} →
    is-equiv
      ( λ H →
        right-whisker-comp {g = g} {h} H
          ( unit-localization-global-subuniverse LX))
  is-equiv-right-whisker-unit-localization-global-subuniverse {g} {h} =
    is-equiv-target-is-equiv-source-equiv-arrow
      ( ap (precomp (unit-localization-global-subuniverse LX) Y))
      ( _·r (unit-localization-global-subuniverse LX))
      ( equiv-funext ,
        equiv-funext ,
        coherence-htpy-eq-ap-precomp' (unit-localization-global-subuniverse LX))
      (is-emb-is-equiv (up-localization-global-subuniverse LX (Y , H)) g h)
```

### A type is a `𝒫`-type if it has a `𝒫`-localization and is a pullback of types in `𝒫`

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 l3 l4 l5 : Level}
  {𝒮 : cospan-diagram l1 l2 l3}
  (c : pullback-cone 𝒮 l4)
  (LC : localization-global-subuniverse 𝒫 l5 (domain-pullback-cone 𝒮 c))
  where

  map-compute-cone-pullback-localization-global-subuniverse :
    cone
      ( left-map-cospan-diagram 𝒮)
      ( right-map-cospan-diagram 𝒮)
      ( type-localization-global-subuniverse LC) →
    cone
      ( left-map-cospan-diagram 𝒮)
      ( right-map-cospan-diagram 𝒮)
      ( domain-pullback-cone 𝒮 c)
  map-compute-cone-pullback-localization-global-subuniverse c' =
    cone-map
      ( left-map-cospan-diagram 𝒮)
      ( right-map-cospan-diagram 𝒮)
      ( c')
      ( unit-localization-global-subuniverse LC)

  is-equiv-map-compute-cone-pullback-localization-global-subuniverse :
    is-in-global-subuniverse 𝒫 (cospanning-type-cospan-diagram 𝒮) →
    is-in-global-subuniverse 𝒫 (domain-cospan-diagram 𝒮) →
    is-in-global-subuniverse 𝒫 (codomain-cospan-diagram 𝒮) →
    is-equiv map-compute-cone-pullback-localization-global-subuniverse
  is-equiv-map-compute-cone-pullback-localization-global-subuniverse x a b =
    is-equiv-map-Σ _
      ( up-localization-global-subuniverse LC
        ( domain-cospan-diagram 𝒮 , a))
      ( λ _ →
        is-equiv-map-Σ _
          ( up-localization-global-subuniverse LC
            ( codomain-cospan-diagram 𝒮 , b))
          ( λ _ →
            is-equiv-right-whisker-unit-localization-global-subuniverse 𝒫 LC x))

  is-in-global-subuniverse-pullback-localization-global-subuniverse :
    is-in-global-subuniverse 𝒫 (cospanning-type-cospan-diagram 𝒮) →
    is-in-global-subuniverse 𝒫 (domain-cospan-diagram 𝒮) →
    is-in-global-subuniverse 𝒫 (codomain-cospan-diagram 𝒮) →
    is-in-global-subuniverse 𝒫 (domain-pullback-cone 𝒮 c)
  is-in-global-subuniverse-pullback-localization-global-subuniverse x a b =
    is-in-global-subuniverse-is-local-type-universal-property-localization-global-subuniverse
      ( 𝒫)
      ( reflection-localization-global-subuniverse LC)
      ( up-localization-global-subuniverse LC)
      ( is-equiv-source-is-equiv-target-equiv-arrow
        ( precomp
          ( unit-localization-global-subuniverse LC)
          ( domain-pullback-cone 𝒮 c))
        ( map-compute-cone-pullback-localization-global-subuniverse)
        ( ( ( cone-map
              ( left-map-cospan-diagram 𝒮)
              ( right-map-cospan-diagram 𝒮)
              ( cone-pullback-cone 𝒮 c)) ,
            ( up-pullback-cone 𝒮 c (type-localization-global-subuniverse LC))) ,
          ( ( cone-map
              ( left-map-cospan-diagram 𝒮)
              ( right-map-cospan-diagram 𝒮)
              ( cone-pullback-cone 𝒮 c)) ,
            ( up-pullback-cone 𝒮 c ( domain-pullback-cone 𝒮 c))) ,
          ( refl-htpy))
        ( is-equiv-map-compute-cone-pullback-localization-global-subuniverse
            ( x)
            ( a)
            ( b)))
```

### Cartesian products of `𝒫`-types that have a `𝒫`-localization are `𝒫`-types

Let `𝒫` be a global subuniverse such that `unit` is a `𝒫`-type. Then if `A` and
`B` are `𝒫`-types and their cartesian product `A × B` has a `𝒫`-localization,
then `A × B` is a `𝒫`-type.

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  (U : is-in-global-subuniverse 𝒫 unit)
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (H : is-in-global-subuniverse 𝒫 A)
  (K : is-in-global-subuniverse 𝒫 B)
  (LI : localization-global-subuniverse 𝒫 l3 (A × B))
  where

  is-in-global-subuniverse-cartesian-product-localization-global-subuniverse :
    is-in-global-subuniverse 𝒫 (A × B)
  is-in-global-subuniverse-cartesian-product-localization-global-subuniverse =
    is-in-global-subuniverse-pullback-localization-global-subuniverse 𝒫
      ( pullback-cone-cartesian-product)
      ( LI)
      ( U)
      ( H)
      ( K)
```

### Identity types of `𝒫`-types that have a `𝒫`-localization are `𝒫`-types

Let `𝒫` be a global subuniverse such that `unit` is a `𝒫`-type. Now assume given
a `𝒫`-type `A` with elements `x` and `y` such that `x ＝ y` has a
`𝒫`-localization, then `x ＝ y` is a `𝒫`-type.

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  (U : is-in-global-subuniverse 𝒫 unit)
  {l1 l2 : Level} {A : UU l1} {x y : A}
  (H : is-in-global-subuniverse 𝒫 A)
  (LI : localization-global-subuniverse 𝒫 l2 (x ＝ y))
  where

  is-in-global-subuniverse-Id-localization-global-subuniverse :
    is-in-global-subuniverse 𝒫 (x ＝ y)
  is-in-global-subuniverse-Id-localization-global-subuniverse =
    is-in-global-subuniverse-pullback-localization-global-subuniverse 𝒫
      ( pullback-cone-Id x y)
      ( LI)
      ( H)
      ( U)
      ( U)
```

### Sequential limits of `𝒫`-types that have a `𝒫`-localization are `𝒫`-types

> This remains to be formalized.

### Cartesian products of `𝒫`-localizations

Let `𝒫` be a global subuniverse, then if `η_A : A → LA` and `η_B : B → LB` are
`𝒫`-localizations such that `LA × LB` is a `𝒫`-type and `𝒫` is closed under
exponentiating by `LB`, then `η_A × η_B : A × B → LA × LB` is a `𝒫`-localization
as well.

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  (LA : localization-global-subuniverse 𝒫 l3 A)
  (LB : localization-global-subuniverse 𝒫 l4 B)
  (exp-LB :
    {l : Level}
    (Z : type-global-subuniverse 𝒫 l) →
    is-in-global-subuniverse 𝒫
      ( type-localization-global-subuniverse LB →
        inclusion-global-subuniverse 𝒫 Z))
  (H :
    is-in-global-subuniverse 𝒫
      ( type-localization-global-subuniverse LA ×
        type-localization-global-subuniverse LB))
  where

  type-cartesian-product-localization-global-subuniverse :
    UU (l3 ⊔ l4)
  type-cartesian-product-localization-global-subuniverse =
    type-localization-global-subuniverse LA ×
    type-localization-global-subuniverse LB

  unit-cartesian-product-localization-global-subuniverse :
    A × B → type-cartesian-product-localization-global-subuniverse
  unit-cartesian-product-localization-global-subuniverse =
    map-product
      ( unit-localization-global-subuniverse LA)
      ( unit-localization-global-subuniverse LB)

  reflection-cartesian-product-localization-global-subuniverse :
    extension-type-global-subuniverse 𝒫 (l3 ⊔ l4) (A × B)
  reflection-cartesian-product-localization-global-subuniverse =
    ( type-cartesian-product-localization-global-subuniverse , H) ,
    ( unit-cartesian-product-localization-global-subuniverse)

  up-cartesian-product-localization-global-subuniverse :
    universal-property-localization-global-subuniverse 𝒫 (A × B)
      ( reflection-cartesian-product-localization-global-subuniverse)
  up-cartesian-product-localization-global-subuniverse Z =
    is-equiv-source-is-equiv-target-equiv-arrow
      ( precomp
        ( unit-cartesian-product-localization-global-subuniverse)
        ( inclusion-global-subuniverse 𝒫 Z))
      ( λ f →
        ( precomp
          ( unit-localization-global-subuniverse LB)
          ( inclusion-global-subuniverse 𝒫 Z)) ∘
        ( precomp
          ( unit-localization-global-subuniverse LA)
          ( type-localization-global-subuniverse LB →
            inclusion-global-subuniverse 𝒫 Z)
          ( f)))
      ( equiv-ev-pair , equiv-ev-pair , refl-htpy)
      ( is-equiv-comp
        ( postcomp A
          ( precomp
            ( unit-localization-global-subuniverse LB)
            ( inclusion-global-subuniverse 𝒫 Z)))
        ( precomp
          ( unit-localization-global-subuniverse LA)
          ( type-localization-global-subuniverse LB →
            inclusion-global-subuniverse 𝒫 Z))
        ( up-localization-global-subuniverse LA
          ( ( type-localization-global-subuniverse LB →
              inclusion-global-subuniverse 𝒫 Z) ,
            ( exp-LB Z)))
        ( is-equiv-postcomp-is-equiv
          ( precomp
            ( unit-localization-global-subuniverse LB)
            ( inclusion-global-subuniverse 𝒫 Z))
          ( up-localization-global-subuniverse LB Z)
          ( A)))

  cartesian-product-localization-global-subuniverse :
    localization-global-subuniverse 𝒫 (l3 ⊔ l4) (A × B)
  reflection-localization-global-subuniverse
    cartesian-product-localization-global-subuniverse =
    reflection-cartesian-product-localization-global-subuniverse
  up-localization-global-subuniverse
    cartesian-product-localization-global-subuniverse =
    up-cartesian-product-localization-global-subuniverse
```

## References

{{#bibliography}}
