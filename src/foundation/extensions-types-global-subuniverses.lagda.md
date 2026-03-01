# Extensions of types in a global subuniverse

```agda
module foundation.extensions-types-global-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.extensions-types
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.global-subuniverses
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels
```

</details>

## Idea

Consider a type `X`. An
{{#concept "extension" Disambiguation="type in global subuniverse" Agda=extension-type-global-subuniverse}}
of `X` in a [global subuniverse](foundation.global-subuniverses.md) `𝒫` is an
object in the coslice under `X` in `𝒫`, i.e., it consists of a type `Y` in `𝒫`
and a map `f : X → Y`.

In the above definition of extensions of types in a global subuniverse our aim
is to capture the most general concept of what it means to be an extension of a
type in a subuniverse.

Our notion of extensions of types are not to be confused with extension types of
cubical type theory or
[extension types of simplicial type theory](https://arxiv.org/abs/1705.07442).

## Definitions

### The predicate on an extension of types of being in a global subuniverse

```agda
module _
  {α : Level → Level} {l1 l2 : Level}
  (𝒫 : global-subuniverse α) {X : UU l1}
  (E : extension-type l2 X)
  where

  is-in-global-subuniverse-extension-type-Prop : Prop (α l2)
  is-in-global-subuniverse-extension-type-Prop =
    is-in-global-subuniverse-Prop 𝒫 (type-extension-type E)

  is-in-global-subuniverse-extension-type : UU (α l2)
  is-in-global-subuniverse-extension-type =
    is-in-global-subuniverse 𝒫 (type-extension-type E)

  is-prop-is-in-global-subuniverse-extension-type :
    is-prop is-in-global-subuniverse-extension-type
  is-prop-is-in-global-subuniverse-extension-type =
    is-prop-is-in-global-subuniverse 𝒫 (type-extension-type E)
```

### Extensions of types in a subuniverse

```agda
extension-type-global-subuniverse :
  {α : Level → Level} {l1 : Level}
  (𝒫 : global-subuniverse α) (l2 : Level) (X : UU l1) →
  UU (α l2 ⊔ l1 ⊔ lsuc l2)
extension-type-global-subuniverse 𝒫 l2 X =
  Σ (type-global-subuniverse 𝒫 l2) (λ Y → X → inclusion-global-subuniverse 𝒫 Y)

module _
  {α : Level → Level} {l1 l2 : Level} (𝒫 : global-subuniverse α) {X : UU l1}
  (Y : extension-type-global-subuniverse 𝒫 l2 X)
  where

  type-global-subuniverse-extension-type-global-subuniverse :
    type-global-subuniverse 𝒫 l2
  type-global-subuniverse-extension-type-global-subuniverse = pr1 Y

  type-extension-type-global-subuniverse : UU l2
  type-extension-type-global-subuniverse =
    inclusion-global-subuniverse 𝒫
      type-global-subuniverse-extension-type-global-subuniverse

  is-in-global-subuniverse-type-extension-type-global-subuniverse :
    is-in-global-subuniverse 𝒫 type-extension-type-global-subuniverse
  is-in-global-subuniverse-type-extension-type-global-subuniverse =
    is-in-global-subuniverse-inclusion-global-subuniverse 𝒫
      type-global-subuniverse-extension-type-global-subuniverse

  inclusion-extension-type-global-subuniverse :
    X → type-extension-type-global-subuniverse
  inclusion-extension-type-global-subuniverse = pr2 Y

  extension-type-extension-type-global-subuniverse : extension-type l2 X
  extension-type-extension-type-global-subuniverse =
    type-extension-type-global-subuniverse ,
    inclusion-extension-type-global-subuniverse
```

## Properties

### Extensions of types in a subuniverse are extensions of types by types in the subuniverse

```agda
module _
  {α : Level → Level} {l1 l2 : Level} (𝒫 : global-subuniverse α) {X : UU l1}
  where

  compute-extension-type-global-subuniverse :
    extension-type-global-subuniverse 𝒫 l2 X ≃
    Σ (extension-type l2 X) (is-in-global-subuniverse-extension-type 𝒫)
  compute-extension-type-global-subuniverse = equiv-right-swap-Σ
```

### The inclusion of extensions of types in a subuniverse into extensions of types is an embedding

```agda
module _
  {α : Level → Level} {l1 l2 : Level} (𝒫 : global-subuniverse α) {X : UU l1}
  where

  compute-fiber-extension-type-extension-type-global-subuniverse :
    (Y : extension-type l2 X) →
    fiber (extension-type-extension-type-global-subuniverse 𝒫) Y ≃
    is-in-global-subuniverse 𝒫 (type-extension-type Y)
  compute-fiber-extension-type-extension-type-global-subuniverse Y =
    equivalence-reasoning
    Σ ( Σ (Σ (UU l2) (λ Z → is-in-global-subuniverse 𝒫 Z)) (λ Z → X → pr1 Z))
      ( λ E → extension-type-extension-type-global-subuniverse 𝒫 E ＝ Y)
    ≃ Σ ( Σ (extension-type l2 X) (is-in-global-subuniverse-extension-type 𝒫))
        ( λ E → pr1 E ＝ Y)
    by
      equiv-Σ-equiv-base
        ( λ E → pr1 E ＝ Y)
        ( compute-extension-type-global-subuniverse 𝒫)
    ≃ Σ ( Σ (extension-type l2 X) (λ E → E ＝ Y))
        ( is-in-global-subuniverse-extension-type 𝒫 ∘ pr1)
      by equiv-right-swap-Σ
    ≃ is-in-global-subuniverse-extension-type 𝒫 Y
    by left-unit-law-Σ-is-contr (is-torsorial-Id' Y) (Y , refl)

  is-prop-map-extension-type-extension-type-global-subuniverse :
    is-prop-map (extension-type-extension-type-global-subuniverse 𝒫)
  is-prop-map-extension-type-extension-type-global-subuniverse Y =
    is-prop-equiv
      ( compute-fiber-extension-type-extension-type-global-subuniverse Y)
      ( is-prop-is-in-global-subuniverse 𝒫 (type-extension-type Y))

  is-emb-extension-type-extension-type-global-subuniverse :
    is-emb (extension-type-extension-type-global-subuniverse 𝒫)
  is-emb-extension-type-extension-type-global-subuniverse =
    is-emb-is-prop-map
      is-prop-map-extension-type-extension-type-global-subuniverse
```

### Characterization of identifications of extensions of types in a subuniverse

```agda
equiv-extension-type-global-subuniverse :
  {α : Level → Level} {l1 l2 l3 : Level}
  (𝒫 : global-subuniverse α) {X : UU l1} →
  extension-type-global-subuniverse 𝒫 l2 X →
  extension-type-global-subuniverse 𝒫 l3 X → UU (l1 ⊔ l2 ⊔ l3)
equiv-extension-type-global-subuniverse 𝒫 U V =
  equiv-extension-type
    ( extension-type-extension-type-global-subuniverse 𝒫 U)
    ( extension-type-extension-type-global-subuniverse 𝒫 V)

module _
  {α : Level → Level} {l1 l2 : Level} (𝒫 : global-subuniverse α) {X : UU l1}
  where

  id-equiv-extension-type-global-subuniverse :
    (U : extension-type-global-subuniverse 𝒫 l2 X) →
    equiv-extension-type-global-subuniverse 𝒫 U U
  id-equiv-extension-type-global-subuniverse U =
    id-equiv-extension-type
      ( extension-type-extension-type-global-subuniverse 𝒫 U)

  equiv-eq-extension-type-global-subuniverse :
    (U V : extension-type-global-subuniverse 𝒫 l2 X) →
    U ＝ V → equiv-extension-type-global-subuniverse 𝒫 U V
  equiv-eq-extension-type-global-subuniverse U V p =
    equiv-eq-extension-type
      ( extension-type-extension-type-global-subuniverse 𝒫 U)
      ( extension-type-extension-type-global-subuniverse 𝒫 V)
      ( ap (extension-type-extension-type-global-subuniverse 𝒫) p)

  is-equiv-equiv-eq-extension-type-global-subuniverse :
    (U V : extension-type-global-subuniverse 𝒫 l2 X) →
    is-equiv (equiv-eq-extension-type-global-subuniverse U V)
  is-equiv-equiv-eq-extension-type-global-subuniverse U V =
    is-equiv-comp
      ( equiv-eq-extension-type
        ( extension-type-extension-type-global-subuniverse 𝒫 U)
        ( extension-type-extension-type-global-subuniverse 𝒫 V))
      ( ap (extension-type-extension-type-global-subuniverse 𝒫))
      ( is-emb-extension-type-extension-type-global-subuniverse 𝒫 U V)
      ( is-equiv-equiv-eq-extension-type
        ( extension-type-extension-type-global-subuniverse 𝒫 U)
        ( extension-type-extension-type-global-subuniverse 𝒫 V))

  extensionality-extension-type-global-subuniverse :
    (U V : extension-type-global-subuniverse 𝒫 l2 X) →
    (U ＝ V) ≃ equiv-extension-type-global-subuniverse 𝒫 U V
  extensionality-extension-type-global-subuniverse U V =
    equiv-eq-extension-type-global-subuniverse U V ,
    is-equiv-equiv-eq-extension-type-global-subuniverse U V

  eq-equiv-extension-type-global-subuniverse :
    (U V : extension-type-global-subuniverse 𝒫 l2 X) →
    equiv-extension-type-global-subuniverse 𝒫 U V → U ＝ V
  eq-equiv-extension-type-global-subuniverse U V =
    map-inv-equiv (extensionality-extension-type-global-subuniverse U V)
```
