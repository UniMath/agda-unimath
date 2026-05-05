# Extensions of types in a subuniverse

```agda
module foundation.extensions-types-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.dependent-products-propositions
open import foundation.embeddings
open import foundation.equivalences
open import foundation.extensions-types
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.subuniverses
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels
```

</details>

## Idea

Consider a type `X`. An
{{#concept "extension" Disambiguation="type in subuniverse" Agda=extension-type-subuniverse}}
of `X` in a [subuniverse](foundation.subuniverses.md) `𝒫` is an object in the
coslice under `X` in `𝒫`, i.e., it consists of a type `Y` in `𝒫` and a map
`f : X → Y`.

In the above definition of extensions of types in a subuniverse our aim is to
capture the most general concept of what it means to be an extension of a type
in a subuniverse.

Our notion of extensions of types are not to be confused with extension types of
cubical type theory or
[extension types of simplicial type theory](https://arxiv.org/abs/1705.07442).

## Definitions

### The predicate on an extension of types of being in a subuniverse

```agda
module _
  {l1 l2 l3 : Level} (𝒫 : subuniverse l1 l2) {X : UU l3}
  (E : extension-type l1 X)
  where

  is-in-subuniverse-extension-type-Prop : Prop l2
  is-in-subuniverse-extension-type-Prop = 𝒫 (type-extension-type E)

  is-in-subuniverse-extension-type : UU l2
  is-in-subuniverse-extension-type =
    is-in-subuniverse 𝒫 (type-extension-type E)

  is-prop-is-in-subuniverse-extension-type :
    is-prop is-in-subuniverse-extension-type
  is-prop-is-in-subuniverse-extension-type =
    is-prop-is-in-subuniverse 𝒫 (type-extension-type E)
```

### Extensions of types in a subuniverse

```agda
extension-type-subuniverse :
  {l1 l2 l3 : Level} (𝒫 : subuniverse l1 l2) (X : UU l3) →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
extension-type-subuniverse 𝒫 X =
  Σ (type-subuniverse 𝒫) (λ Y → X → inclusion-subuniverse 𝒫 Y)

module _
  {l1 l2 l3 : Level} (𝒫 : subuniverse l1 l2) {X : UU l3}
  (Y : extension-type-subuniverse 𝒫 X)
  where

  type-subuniverse-extension-type-subuniverse : type-subuniverse 𝒫
  type-subuniverse-extension-type-subuniverse = pr1 Y

  type-extension-type-subuniverse : UU l1
  type-extension-type-subuniverse =
    inclusion-subuniverse 𝒫 type-subuniverse-extension-type-subuniverse

  is-in-subuniverse-type-extension-type-subuniverse :
    is-in-subuniverse 𝒫 type-extension-type-subuniverse
  is-in-subuniverse-type-extension-type-subuniverse =
    is-in-subuniverse-inclusion-subuniverse 𝒫
      type-subuniverse-extension-type-subuniverse

  inclusion-extension-type-subuniverse : X → type-extension-type-subuniverse
  inclusion-extension-type-subuniverse = pr2 Y

  extension-type-extension-type-subuniverse : extension-type l1 X
  extension-type-extension-type-subuniverse =
    type-extension-type-subuniverse , inclusion-extension-type-subuniverse
```

## Properties

### Extensions of types in a subuniverse are extensions of types by types in the subuniverse

```agda
module _
  {l1 l2 l3 : Level} (𝒫 : subuniverse l1 l2) {X : UU l3}
  where

  compute-extension-type-subuniverse :
    extension-type-subuniverse 𝒫 X ≃
    Σ (extension-type l1 X) (is-in-subuniverse-extension-type 𝒫)
  compute-extension-type-subuniverse = equiv-right-swap-Σ
```

### The inclusion of extensions of types in a subuniverse into extensions of types is an embedding

```agda
module _
  {l1 l2 l3 : Level} (𝒫 : subuniverse l1 l2) {X : UU l3}
  where

  compute-fiber-extension-type-extension-type-subuniverse :
    (Y : extension-type l1 X) →
    fiber (extension-type-extension-type-subuniverse 𝒫) Y ≃
    is-in-subuniverse 𝒫 (type-extension-type Y)
  compute-fiber-extension-type-extension-type-subuniverse Y =
    equivalence-reasoning
    Σ ( Σ (Σ (UU l1) (λ Z → is-in-subuniverse 𝒫 Z)) (λ Z → X → pr1 Z))
      ( λ E → extension-type-extension-type-subuniverse 𝒫 E ＝ Y)
    ≃ Σ ( Σ (extension-type l1 X) (is-in-subuniverse-extension-type 𝒫))
        ( λ E → pr1 E ＝ Y)
    by
      equiv-Σ-equiv-base
        ( λ E → pr1 E ＝ Y)
        ( compute-extension-type-subuniverse 𝒫)
    ≃ Σ ( Σ (extension-type l1 X) (λ E → E ＝ Y))
        ( is-in-subuniverse-extension-type 𝒫 ∘ pr1)
      by equiv-right-swap-Σ
    ≃ is-in-subuniverse-extension-type 𝒫 Y
    by left-unit-law-Σ-is-contr (is-torsorial-Id' Y) (Y , refl)

  is-prop-map-extension-type-extension-type-subuniverse :
    is-prop-map (extension-type-extension-type-subuniverse 𝒫)
  is-prop-map-extension-type-extension-type-subuniverse Y =
    is-prop-equiv
      ( compute-fiber-extension-type-extension-type-subuniverse Y)
      ( is-prop-is-in-subuniverse 𝒫 (type-extension-type Y))

  is-emb-extension-type-extension-type-subuniverse :
    is-emb (extension-type-extension-type-subuniverse 𝒫)
  is-emb-extension-type-extension-type-subuniverse =
    is-emb-is-prop-map is-prop-map-extension-type-extension-type-subuniverse
```

### Characterization of identifications of extensions of types in a subuniverse

```agda
module _
  {l1 l2 l3 : Level} (𝒫 : subuniverse l1 l2) {X : UU l3}
  where

  equiv-extension-type-subuniverse :
    extension-type-subuniverse 𝒫 X →
    extension-type-subuniverse 𝒫 X → UU (l1 ⊔ l3)
  equiv-extension-type-subuniverse U V =
    equiv-extension-type
      ( extension-type-extension-type-subuniverse 𝒫 U)
      ( extension-type-extension-type-subuniverse 𝒫 V)

  id-equiv-extension-type-subuniverse :
    (U : extension-type-subuniverse 𝒫 X) → equiv-extension-type-subuniverse U U
  id-equiv-extension-type-subuniverse U =
    id-equiv-extension-type (extension-type-extension-type-subuniverse 𝒫 U)

  equiv-eq-extension-type-subuniverse :
    (U V : extension-type-subuniverse 𝒫 X) →
    U ＝ V → equiv-extension-type-subuniverse U V
  equiv-eq-extension-type-subuniverse U V p =
    equiv-eq-extension-type
      ( extension-type-extension-type-subuniverse 𝒫 U)
      ( extension-type-extension-type-subuniverse 𝒫 V)
      ( ap (extension-type-extension-type-subuniverse 𝒫) p)

  is-equiv-equiv-eq-extension-type-subuniverse :
    (U V : extension-type-subuniverse 𝒫 X) →
    is-equiv (equiv-eq-extension-type-subuniverse U V)
  is-equiv-equiv-eq-extension-type-subuniverse U V =
    is-equiv-comp
      ( equiv-eq-extension-type
        ( extension-type-extension-type-subuniverse 𝒫 U)
        ( extension-type-extension-type-subuniverse 𝒫 V))
      ( ap (extension-type-extension-type-subuniverse 𝒫))
      ( is-emb-extension-type-extension-type-subuniverse 𝒫 U V)
      ( is-equiv-equiv-eq-extension-type
        ( extension-type-extension-type-subuniverse 𝒫 U)
        ( extension-type-extension-type-subuniverse 𝒫 V))

  extensionality-extension-type-subuniverse :
    (U V : extension-type-subuniverse 𝒫 X) →
    (U ＝ V) ≃ equiv-extension-type-subuniverse U V
  extensionality-extension-type-subuniverse U V =
    equiv-eq-extension-type-subuniverse U V ,
    is-equiv-equiv-eq-extension-type-subuniverse U V

  eq-equiv-extension-type-subuniverse :
    (U V : extension-type-subuniverse 𝒫 X) →
    equiv-extension-type-subuniverse U V → U ＝ V
  eq-equiv-extension-type-subuniverse U V =
    map-inv-equiv (extensionality-extension-type-subuniverse U V)
```
