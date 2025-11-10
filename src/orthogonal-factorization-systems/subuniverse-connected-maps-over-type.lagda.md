# Connected maps with respect to a subuniverse over a type

```agda
module orthogonal-factorization-systems.subuniverse-connected-maps-over-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.connected-types
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.inhabited-types
open import foundation.iterated-successors-truncation-levels
open import foundation.postcomposition-functions
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.precomposition-type-families
open import foundation.propositional-truncations
open import foundation.retracts-of-maps
open import foundation.sections
open import foundation.split-surjective-maps
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.subuniverses
open import foundation.surjective-maps
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.unit-type
open import foundation.univalence
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.postcomposition-dependent-functions
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-maps

open import orthogonal-factorization-systems.extensions-maps
open import orthogonal-factorization-systems.localizations-at-subuniverses
open import orthogonal-factorization-systems.orthogonal-maps
open import orthogonal-factorization-systems.subuniverse-connected-maps
open import orthogonal-factorization-systems.subuniverse-connected-types
open import orthogonal-factorization-systems.subuniverse-equivalences

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-pullback-property-pushouts
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

Given a [subuniverse](foundation.subuniverses.md) `K` we consider the type of
`K`-connected maps over a type `X`.

## Definitions

### The type of `K`-connected maps over a type

```agda
Subuniverse-Connected-Map :
  {l1 l2 l3 : Level} (l4 : Level) (K : subuniverse l1 l2) (A : UU l3) →
  UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4)
Subuniverse-Connected-Map l2 K A = Σ (UU l2) (subuniverse-connected-map K A)

module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2)
  {A : UU l3} (f : Subuniverse-Connected-Map l4 K A)
  where

  type-Subuniverse-Connected-Map : UU l4
  type-Subuniverse-Connected-Map = pr1 f

  subuniverse-connected-map-Subuniverse-Connected-Map :
    subuniverse-connected-map K A type-Subuniverse-Connected-Map
  subuniverse-connected-map-Subuniverse-Connected-Map = pr2 f

  map-Subuniverse-Connected-Map : A → type-Subuniverse-Connected-Map
  map-Subuniverse-Connected-Map =
    map-subuniverse-connected-map K
      ( subuniverse-connected-map-Subuniverse-Connected-Map)

  is-subuniverse-connected-map-Subuniverse-Connected-Map :
    is-subuniverse-connected-map K map-Subuniverse-Connected-Map
  is-subuniverse-connected-map-Subuniverse-Connected-Map =
    is-subuniverse-connected-map-subuniverse-connected-map K
      ( subuniverse-connected-map-Subuniverse-Connected-Map)
```

## Properties

### Characterization of equality of `Subuniverse-Connected-Map l4 K A`

```agda
equiv-Subuniverse-Connected-Map :
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2) {A : UU l3} →
  (f g : Subuniverse-Connected-Map l4 K A) → UU (l3 ⊔ l4)
equiv-Subuniverse-Connected-Map K f g =
  Σ ( type-Subuniverse-Connected-Map K f ≃ type-Subuniverse-Connected-Map K g)
    ( λ e →
      map-equiv e ∘ map-Subuniverse-Connected-Map K f ~
      map-Subuniverse-Connected-Map K g)

module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2) {A : UU l3}
  (f : Subuniverse-Connected-Map l4 K A)
  where

  id-equiv-Subuniverse-Connected-Map : equiv-Subuniverse-Connected-Map K f f
  id-equiv-Subuniverse-Connected-Map = (id-equiv , refl-htpy)

  is-torsorial-equiv-Subuniverse-Connected-Map :
    is-torsorial (equiv-Subuniverse-Connected-Map K f)
  is-torsorial-equiv-Subuniverse-Connected-Map =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv (type-Subuniverse-Connected-Map K f))
      ( type-Subuniverse-Connected-Map K f , id-equiv)
      ( is-torsorial-htpy-subuniverse-connected-map K
        ( subuniverse-connected-map-Subuniverse-Connected-Map K f))

  equiv-eq-Subuniverse-Connected-Map :
    (g : Subuniverse-Connected-Map l4 K A) →
    f ＝ g → equiv-Subuniverse-Connected-Map K f g
  equiv-eq-Subuniverse-Connected-Map .f refl =
    id-equiv-Subuniverse-Connected-Map

  is-equiv-equiv-eq-Subuniverse-Connected-Map :
    (g : Subuniverse-Connected-Map l4 K A) →
    is-equiv (equiv-eq-Subuniverse-Connected-Map g)
  is-equiv-equiv-eq-Subuniverse-Connected-Map =
    fundamental-theorem-id
      ( is-torsorial-equiv-Subuniverse-Connected-Map)
      ( equiv-eq-Subuniverse-Connected-Map)

  extensionality-Subuniverse-Connected-Map :
    (g : Subuniverse-Connected-Map l4 K A) →
    (f ＝ g) ≃ equiv-Subuniverse-Connected-Map K f g
  extensionality-Subuniverse-Connected-Map g =
    ( equiv-eq-Subuniverse-Connected-Map g ,
      is-equiv-equiv-eq-Subuniverse-Connected-Map g)

  eq-equiv-Subuniverse-Connected-Map :
    (g : Subuniverse-Connected-Map l4 K A) →
    equiv-Subuniverse-Connected-Map K f g → f ＝ g
  eq-equiv-Subuniverse-Connected-Map g =
    map-inv-equiv (extensionality-Subuniverse-Connected-Map g)
```
