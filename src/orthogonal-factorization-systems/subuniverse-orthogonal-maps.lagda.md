# `K`-orthogonal maps, with respect to a subuniverse `K`

```agda
module orthogonal-factorization-systems.subuniverse-orthogonal-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.subuniverses
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.retractions
open import foundation-core.sections

open import orthogonal-factorization-systems.extensions-maps
open import orthogonal-factorization-systems.orthogonal-maps
open import orthogonal-factorization-systems.subuniverse-connected-maps
```

</details>

## Idea

Given a [subuniverse](foundation.subuniverses.md) `K`, a map `f : A → B` is said
to be
{{#concept "`K`-orthogonal" Disambiguation="map of types, with respect to a subuniverse" Agda=is-subuniverse-orthogonal-map}}
if it is [right orthogonal](orthogonal-factorization-systems.orthogonal-maps.md)
to every
`K`-[connected map](orthogonal-factorization-systems.subuniverse-connected-maps.md).

## Definitions

### The predicate on a map of being `K`-orthogonal with respect to a pair of universe levels

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} (f : A → B)
  where

  is-subuniverse-orthogonal-map-Level :
    (l5 l6 : Level) → UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5 ⊔ lsuc l6)
  is-subuniverse-orthogonal-map-Level l5 l6 =
    {X : UU l5} {Y : UU l6} (g : subuniverse-connected-map K X Y) →
    is-orthogonal (map-subuniverse-connected-map K g) f

  is-prop-is-subuniverse-orthogonal-map-Level :
    {l5 l6 : Level} → is-prop (is-subuniverse-orthogonal-map-Level l5 l6)
  is-prop-is-subuniverse-orthogonal-map-Level =
    is-prop-implicit-Π
      ( λ X →
        is-prop-implicit-Π
        ( λ Y →
          is-prop-Π
            ( λ g →
              is-prop-is-orthogonal (map-subuniverse-connected-map K g) f)))

  is-subuniverse-orthogonal-map-prop-Level :
    (l5 l6 : Level) → Prop (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5 ⊔ lsuc l6)
  is-subuniverse-orthogonal-map-prop-Level l5 l6 =
    ( is-subuniverse-orthogonal-map-Level l5 l6 ,
      is-prop-is-subuniverse-orthogonal-map-Level)
```
