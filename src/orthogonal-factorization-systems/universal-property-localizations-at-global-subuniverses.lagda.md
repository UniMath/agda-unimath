# The universal property of localizations at global subuniverses

```agda
module orthogonal-factorization-systems.universal-property-localizations-at-global-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.dependent-products-propositions
open import foundation.equivalences
open import foundation.extensions-types
open import foundation.extensions-types-global-subuniverses
open import foundation.function-extensionality-axiom
open import foundation.function-types
open import foundation.global-subuniverses
open import foundation.identity-types
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.univalence
open import foundation.universe-levels

open import orthogonal-factorization-systems.extensions-dependent-maps
open import orthogonal-factorization-systems.extensions-maps
open import orthogonal-factorization-systems.types-local-at-maps
```

</details>

## Idea

Let `𝒫` be a [global subuniverse](foundation.global-subuniverses.md). Given a
type `X` we say a type `LX` in `𝒫` [equipped](foundation.structure.md) with a
unit map `η : X → LX` satisfies the
{{#concept "universal property of localizations" Disambiguation="at a global universe of types" Agda=universal-property-localization-global-subuniverse}}
if every type `Z` in `𝒫` is
`η`-[local](orthogonal-factorization-systems.types-local-at-maps.md). I.e., the
[precomposition map](foundation-core.function-types.md)

```text
  - ∘ η : (LX → Z) → (X → Z)
```

is an [equivalence](foundation-core.equivalences.md).

## Definitions

### The universal property of being a localization at a global subuniverse

```agda
module _
  {α : Level → Level} {l1 l2 : Level} (𝒫 : global-subuniverse α)
  (X : UU l1) (LX : extension-type-global-subuniverse 𝒫 l2 X)
  where

  universal-property-localization-global-subuniverse-Level :
    (l : Level) → UU (α l ⊔ l1 ⊔ l2 ⊔ lsuc l)
  universal-property-localization-global-subuniverse-Level l =
    (Z : type-global-subuniverse 𝒫 l) →
    is-local
      ( inclusion-extension-type-global-subuniverse 𝒫 LX)
      ( inclusion-global-subuniverse 𝒫 Z)

  universal-property-localization-global-subuniverse : UUω
  universal-property-localization-global-subuniverse =
    {l : Level} → universal-property-localization-global-subuniverse-Level l
```

### The recursion principle of localization at a global subuniverse

```agda
module _
  {α : Level → Level} {l1 l2 : Level} (𝒫 : global-subuniverse α)
  (X : UU l1) (LX : extension-type-global-subuniverse 𝒫 l2 X)
  where

  recursion-principle-localization-global-subuniverse-Level :
    (l : Level) → UU (α l ⊔ l1 ⊔ l2 ⊔ lsuc l)
  recursion-principle-localization-global-subuniverse-Level l =
    (Z : type-global-subuniverse 𝒫 l) →
    section
      ( precomp
        ( inclusion-extension-type-global-subuniverse 𝒫 LX)
        ( inclusion-global-subuniverse 𝒫 Z))

  recursion-principle-localization-global-subuniverse : UUω
  recursion-principle-localization-global-subuniverse =
    {l : Level} → recursion-principle-localization-global-subuniverse-Level l
```

## Properties

### Equivalences satisfy the universal property of localizations

```agda
module _
  {α : Level → Level} {l1 l2 : Level} (𝒫 : global-subuniverse α)
  (X : UU l1) (LX : extension-type-global-subuniverse 𝒫 l2 X)
  where

  universal-property-localization-global-subuniverse-is-equiv :
    is-equiv (inclusion-extension-type-global-subuniverse 𝒫 LX) →
    universal-property-localization-global-subuniverse 𝒫 X LX
  universal-property-localization-global-subuniverse-is-equiv H Z =
    is-local-is-equiv
      ( inclusion-extension-type-global-subuniverse 𝒫 LX)
      ( H)
      ( inclusion-global-subuniverse 𝒫 Z)

module _
  {α : Level → Level} {l1 : Level} (𝒫 : global-subuniverse α)
  (X : type-global-subuniverse 𝒫 l1)
  where

  universal-property-localization-global-subuniverse-id :
    universal-property-localization-global-subuniverse 𝒫
      ( inclusion-global-subuniverse 𝒫 X)
      ( X , id)
  universal-property-localization-global-subuniverse-id =
    universal-property-localization-global-subuniverse-is-equiv 𝒫
      ( inclusion-global-subuniverse 𝒫 X)
      ( X , id)
      ( is-equiv-id)
```

### Satisfying the universal property of localizations is a property

```agda
module _
  {α : Level → Level} {l1 l2 : Level} (𝒫 : global-subuniverse α)
  (X : UU l1) (LX : extension-type-global-subuniverse 𝒫 l2 X)
  where

  is-prop-universal-property-localization-global-subuniverse-Level :
    {l : Level} →
    is-prop (universal-property-localization-global-subuniverse-Level 𝒫 X LX l)
  is-prop-universal-property-localization-global-subuniverse-Level =
    is-prop-Π
      ( λ Z →
        is-property-is-local
          ( inclusion-extension-type-global-subuniverse 𝒫 LX)
          ( inclusion-global-subuniverse 𝒫 Z))
```

### Localizations are closed under equivalences

```agda
module _
  {α : Level → Level} {l1 l2 : Level} (𝒫 : global-subuniverse α)
  (X : UU l1) (LX : extension-type-global-subuniverse 𝒫 l2 X)
  (H : universal-property-localization-global-subuniverse 𝒫 X LX)
  where

  equiv-universal-property-localization-global-subuniverse :
    {l3 : Level} {Y : UU l3}
    (e : type-extension-type-global-subuniverse 𝒫 LX ≃ Y) →
    universal-property-localization-global-subuniverse 𝒫 X
      ( ( Y ,
          is-closed-under-equiv-global-subuniverse 𝒫
            ( type-extension-type-global-subuniverse 𝒫 LX)
            ( Y)
            ( e)
            ( is-in-global-subuniverse-type-extension-type-global-subuniverse
              ( 𝒫)
              ( LX))) ,
        ( map-equiv e ∘ inclusion-extension-type-global-subuniverse 𝒫 LX))
  equiv-universal-property-localization-global-subuniverse e Z =
    is-local-comp
      ( is-local-is-equiv _
        ( is-equiv-map-equiv e)
        ( inclusion-global-subuniverse 𝒫 Z))
      ( H Z)
```

### Localizations are maps with unique extensions

The map `η : X → LX` satisfies the universal property of localizations with
respect to `𝒫` if and only if every map `f : X → Z` where `Z` is in `𝒫` has a
unique extension along `η`

```text
        f
    X ----> Z
    |      ∧
  η |    ⋰
    ∨  ⋰
    LX.
```

```agda
module _
  {α : Level → Level} {l1 l2 : Level} (𝒫 : global-subuniverse α)
  (X : UU l1) (LX : extension-type-global-subuniverse 𝒫 l2 X)
  where

  forward-implication-iff-unique-extensions-universal-property-localization-global-subuniverse :
    universal-property-localization-global-subuniverse 𝒫 X LX →
    {l : Level} (Z : type-global-subuniverse 𝒫 l)
    (f : X → inclusion-global-subuniverse 𝒫 Z) →
    is-contr
      ( extension-map (inclusion-extension-type-global-subuniverse 𝒫 LX) f)
  forward-implication-iff-unique-extensions-universal-property-localization-global-subuniverse
    H Z =
    is-contr-extension-map-is-local
      ( inclusion-extension-type-global-subuniverse 𝒫 LX)
      ( H Z)

  backward-implication-iff-unique-extensions-universal-property-localization-global-subuniverse :
    ( {l : Level} (Z : type-global-subuniverse 𝒫 l)
      (f : X → inclusion-global-subuniverse 𝒫 Z) →
      is-contr
        ( extension-map (inclusion-extension-type-global-subuniverse 𝒫 LX) f)) →
    universal-property-localization-global-subuniverse 𝒫 X LX
  backward-implication-iff-unique-extensions-universal-property-localization-global-subuniverse
    H Z =
    is-local-is-contr-extension-map
      ( inclusion-extension-type-global-subuniverse 𝒫 LX)
      ( H Z)
```

### Localizations are essentially unique

This is Proposition 5.1.2 in {{#cite Rij19}}. We formalize essential uniqueness
with equivalences of extensions of the type `X`, as the universal property is a
large proposition.

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 l3 : Level} {X : UU l1}
  (LX : extension-type-global-subuniverse 𝒫 l2 X)
  (LX' : extension-type-global-subuniverse 𝒫 l3 X)
  (H : universal-property-localization-global-subuniverse 𝒫 X LX)
  (H' : universal-property-localization-global-subuniverse 𝒫 X LX')
  where

  extension-map-essentially-unique-universal-property-localization-global-subuniverse :
    extension-map
      ( inclusion-extension-type-global-subuniverse 𝒫 LX)
      ( inclusion-extension-type-global-subuniverse 𝒫 LX')
  extension-map-essentially-unique-universal-property-localization-global-subuniverse =
    center
      ( forward-implication-iff-unique-extensions-universal-property-localization-global-subuniverse
        ( 𝒫)
        ( X)
        ( LX)
        ( H)
        ( type-global-subuniverse-extension-type-global-subuniverse 𝒫 LX')
        ( inclusion-extension-type-global-subuniverse 𝒫 LX'))

  extension-map-inv-essentially-unique-universal-property-localization-global-subuniverse :
    extension-map
      ( inclusion-extension-type-global-subuniverse 𝒫 LX')
      ( inclusion-extension-type-global-subuniverse 𝒫 LX)
  extension-map-inv-essentially-unique-universal-property-localization-global-subuniverse =
    center
      ( forward-implication-iff-unique-extensions-universal-property-localization-global-subuniverse
        ( 𝒫)
        ( X)
        ( LX')
        ( H')
        ( type-global-subuniverse-extension-type-global-subuniverse 𝒫 LX)
        ( inclusion-extension-type-global-subuniverse 𝒫 LX))

  map-essentially-unique-universal-property-localization-global-subuniverse :
    type-extension-type-global-subuniverse 𝒫 LX →
    type-extension-type-global-subuniverse 𝒫 LX'
  map-essentially-unique-universal-property-localization-global-subuniverse =
    map-extension-map
      extension-map-essentially-unique-universal-property-localization-global-subuniverse

  map-inv-essentially-unique-universal-property-localization-global-subuniverse :
    type-extension-type-global-subuniverse 𝒫 LX' →
    type-extension-type-global-subuniverse 𝒫 LX
  map-inv-essentially-unique-universal-property-localization-global-subuniverse =
    map-extension-map
      extension-map-inv-essentially-unique-universal-property-localization-global-subuniverse

  abstract
    is-section-map-inv-essentially-unique-universal-property-localization-global-subuniverse :
      is-section
        map-essentially-unique-universal-property-localization-global-subuniverse
        map-inv-essentially-unique-universal-property-localization-global-subuniverse
    is-section-map-inv-essentially-unique-universal-property-localization-global-subuniverse =
      htpy-eq
        ( ap
          ( map-extension-map)
          ( eq-is-contr
            ( forward-implication-iff-unique-extensions-universal-property-localization-global-subuniverse
              ( 𝒫)
              ( X)
              ( LX')
              ( H')
              ( type-global-subuniverse-extension-type-global-subuniverse 𝒫 LX')
              ( inclusion-extension-type-global-subuniverse 𝒫 LX'))
            { map-essentially-unique-universal-property-localization-global-subuniverse ∘
              map-inv-essentially-unique-universal-property-localization-global-subuniverse ,
              is-extension-of-map-comp-horizontal
                { f = inclusion-extension-type-global-subuniverse 𝒫 LX'}
                { inclusion-extension-type-global-subuniverse 𝒫 LX}
                { inclusion-extension-type-global-subuniverse 𝒫 LX'}
                { map-inv-essentially-unique-universal-property-localization-global-subuniverse}
                { map-essentially-unique-universal-property-localization-global-subuniverse}
                ( is-extension-map-extension-map
                    extension-map-inv-essentially-unique-universal-property-localization-global-subuniverse)
                ( is-extension-map-extension-map
                    extension-map-essentially-unique-universal-property-localization-global-subuniverse)}
            { self-extension-map
              ( inclusion-extension-type-global-subuniverse 𝒫 LX')}))

  abstract
    is-retraction-map-inv-essentially-unique-universal-property-localization-global-subuniverse :
      is-retraction
        map-essentially-unique-universal-property-localization-global-subuniverse
        map-inv-essentially-unique-universal-property-localization-global-subuniverse
    is-retraction-map-inv-essentially-unique-universal-property-localization-global-subuniverse =
      htpy-eq
        ( ap
          ( map-extension-map)
          ( eq-is-contr
            ( forward-implication-iff-unique-extensions-universal-property-localization-global-subuniverse
              ( 𝒫)
              ( X)
              ( LX)
              ( H)
              ( type-global-subuniverse-extension-type-global-subuniverse 𝒫 LX)
              ( inclusion-extension-type-global-subuniverse 𝒫 LX))
            { map-inv-essentially-unique-universal-property-localization-global-subuniverse ∘
              map-essentially-unique-universal-property-localization-global-subuniverse ,
              is-extension-of-map-comp-horizontal
                { f = inclusion-extension-type-global-subuniverse 𝒫 LX}
                { inclusion-extension-type-global-subuniverse 𝒫 LX'}
                { inclusion-extension-type-global-subuniverse 𝒫 LX}
                { map-essentially-unique-universal-property-localization-global-subuniverse}
                { map-inv-essentially-unique-universal-property-localization-global-subuniverse}
                ( is-extension-map-extension-map
                    extension-map-essentially-unique-universal-property-localization-global-subuniverse)
                ( is-extension-map-extension-map
                    extension-map-inv-essentially-unique-universal-property-localization-global-subuniverse)}
            { self-extension-map
              ( inclusion-extension-type-global-subuniverse 𝒫 LX)}))

  is-equiv-map-essentially-unique-universal-property-localization-global-subuniverse :
    is-equiv
      map-essentially-unique-universal-property-localization-global-subuniverse
  is-equiv-map-essentially-unique-universal-property-localization-global-subuniverse =
    is-equiv-is-invertible
      map-inv-essentially-unique-universal-property-localization-global-subuniverse
      is-section-map-inv-essentially-unique-universal-property-localization-global-subuniverse
      is-retraction-map-inv-essentially-unique-universal-property-localization-global-subuniverse

  essentially-unique-type-universal-property-localization-global-subuniverse :
    type-extension-type-global-subuniverse 𝒫 LX ≃
    type-extension-type-global-subuniverse 𝒫 LX'
  essentially-unique-type-universal-property-localization-global-subuniverse =
    map-essentially-unique-universal-property-localization-global-subuniverse ,
    is-equiv-map-essentially-unique-universal-property-localization-global-subuniverse

  essentially-unique-extension-type-universal-property-localization-global-subuniverse :
    equiv-extension-type-global-subuniverse 𝒫 LX LX'
  essentially-unique-extension-type-universal-property-localization-global-subuniverse =
    essentially-unique-type-universal-property-localization-global-subuniverse ,
    is-extension-map-extension-map
      extension-map-essentially-unique-universal-property-localization-global-subuniverse
```

### Localizations are unique

We formalize uniqueness with equality of extensions of the type `X`, as the
universal property, that after all is a proposition, is large.

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 : Level} {X : UU l1}
  (LX LX' : extension-type-global-subuniverse 𝒫 l2 X)
  (H : universal-property-localization-global-subuniverse 𝒫 X LX)
  (H' : universal-property-localization-global-subuniverse 𝒫 X LX')
  where

  unique-type-universal-property-localization-global-subuniverse :
    type-extension-type-global-subuniverse 𝒫 LX ＝
    type-extension-type-global-subuniverse 𝒫 LX'
  unique-type-universal-property-localization-global-subuniverse =
    eq-equiv
      ( essentially-unique-type-universal-property-localization-global-subuniverse
        ( 𝒫)
        ( LX)
        ( LX')
        ( H)
        ( H'))

  unique-extension-type-universal-property-localization-global-subuniverse :
    LX ＝ LX'
  unique-extension-type-universal-property-localization-global-subuniverse =
    eq-equiv-extension-type-global-subuniverse 𝒫 LX LX'
      ( essentially-unique-extension-type-universal-property-localization-global-subuniverse
        ( 𝒫)
        ( LX)
        ( LX')
        ( H)
        ( H'))
```

### Equivalent conditions for the unit of the localization being an equivalence

Let `η : X → LX` be a localization of `X` at `𝒫`, then the following are
logically equivalent conditions:

1. The type `X` is contained in `𝒫`.
2. The map `η` is an equivalence.
3. The type `X` is local at `η`.
4. The map `η` has a retraction.
5. The precomposition map `- ∘ η` has a section at `X`.

This is Proposition 5.1.3 in {{#cite Rij19}}.

#### A type with a `𝒫`-localization is in `𝒫` if and only if the unit is an equivalence

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 : Level} {X : UU l1}
  (LX : extension-type-global-subuniverse 𝒫 l2 X)
  (H : universal-property-localization-global-subuniverse 𝒫 X LX)
  where

  is-in-global-subuniverse-is-equiv-unit-universal-property-localization-global-subuniverse :
    is-equiv (inclusion-extension-type-global-subuniverse 𝒫 LX) →
    is-in-global-subuniverse 𝒫 X
  is-in-global-subuniverse-is-equiv-unit-universal-property-localization-global-subuniverse
    K =
    is-closed-under-equiv-global-subuniverse 𝒫
      ( type-extension-type-global-subuniverse 𝒫 LX)
      ( X)
      ( inv-equiv (inclusion-extension-type-global-subuniverse 𝒫 LX , K))
      ( is-in-global-subuniverse-type-extension-type-global-subuniverse 𝒫 LX)

  is-equiv-unit-is-in-global-subuniverse-universal-property-localization-global-subuniverse :
    is-in-global-subuniverse 𝒫 X →
    is-equiv (inclusion-extension-type-global-subuniverse 𝒫 LX)
  is-equiv-unit-is-in-global-subuniverse-universal-property-localization-global-subuniverse
    K =
    is-equiv-inclusion-extension-type-equiv
      ( extension-type-extension-type-global-subuniverse 𝒫 LX)
      ( X , id)
      ( essentially-unique-extension-type-universal-property-localization-global-subuniverse
        ( 𝒫)
        ( LX)
        ( ( X , K) , id)
        ( H)
        ( universal-property-localization-global-subuniverse-id 𝒫 (X , K)))
      ( is-equiv-id)
```

#### The unit of a `𝒫`-localization is an equivalence if and only if the type is local at the unit

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 : Level} {X : UU l1}
  (LX : extension-type-global-subuniverse 𝒫 l2 X)
  (H : universal-property-localization-global-subuniverse 𝒫 X LX)
  where

  is-equiv-unit-is-local-type-universal-property-localization-global-subuniverse :
    is-local (inclusion-extension-type-global-subuniverse 𝒫 LX) X →
    is-equiv (inclusion-extension-type-global-subuniverse 𝒫 LX)
  is-equiv-unit-is-local-type-universal-property-localization-global-subuniverse
    K =
    is-equiv-is-local-domains
      ( inclusion-extension-type-global-subuniverse 𝒫 LX)
      ( K)
      ( H (type-global-subuniverse-extension-type-global-subuniverse 𝒫 LX))

  is-local-type-is-equiv-unit-universal-property-localization-global-subuniverse :
    is-equiv (inclusion-extension-type-global-subuniverse 𝒫 LX) →
    is-local (inclusion-extension-type-global-subuniverse 𝒫 LX) X
  is-local-type-is-equiv-unit-universal-property-localization-global-subuniverse
    K =
    H ( X ,
        is-in-global-subuniverse-is-equiv-unit-universal-property-localization-global-subuniverse
          𝒫 LX H K)

  is-in-global-subuniverse-is-local-type-universal-property-localization-global-subuniverse :
    is-local (inclusion-extension-type-global-subuniverse 𝒫 LX) X →
    is-in-global-subuniverse 𝒫 X
  is-in-global-subuniverse-is-local-type-universal-property-localization-global-subuniverse
    K =
    is-in-global-subuniverse-is-equiv-unit-universal-property-localization-global-subuniverse
      ( 𝒫)
      ( LX)
      ( H)
      ( is-equiv-unit-is-local-type-universal-property-localization-global-subuniverse
        ( K))
```

#### The unit of a `𝒫`-localization is an equivalence if and only if it has a retraction

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 : Level} {X : UU l1}
  (LX : extension-type-global-subuniverse 𝒫 l2 X)
  (H : universal-property-localization-global-subuniverse 𝒫 X LX)
  where

  is-equiv-unit-retraction-universal-property-localization-global-subuniverse :
    retraction (inclusion-extension-type-global-subuniverse 𝒫 LX) →
    is-equiv (inclusion-extension-type-global-subuniverse 𝒫 LX)
  is-equiv-unit-retraction-universal-property-localization-global-subuniverse
    r =
    is-equiv-retraction-is-local-codomain
      ( inclusion-extension-type-global-subuniverse 𝒫 LX)
      ( r)
      ( H (type-global-subuniverse-extension-type-global-subuniverse 𝒫 LX))
```

## References

{{#bibliography}}
