# Functoriality of sequential limits

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.functoriality-sequential-limits
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cones-over-inverse-sequential-diagrams funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.inverse-sequential-diagrams funext univalence truncations
open import foundation.morphisms-inverse-sequential-diagrams funext univalence truncations
open import foundation.sequential-limits funext univalence truncations
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
```

</details>

## Idea

The construction of the [sequential limit](foundation.sequential-limits.md) is
functorial.

## Definitions

### The functorial action on maps of standard sequential limits

```agda
module _
  {l1 l2 : Level}
  {A : inverse-sequential-diagram l1} {A' : inverse-sequential-diagram l2}
  where

  map-hom-standard-sequential-limit :
    hom-inverse-sequential-diagram A' A →
    standard-sequential-limit A' →
    standard-sequential-limit A
  pr1 (map-hom-standard-sequential-limit (f , F) (x , H)) n = f n (x n)
  pr2 (map-hom-standard-sequential-limit (f , F) (x , H)) n =
    ap (f n) (H n) ∙ F n (x (succ-ℕ n))

  map-hom-is-sequential-limit :
    {l4 l4' : Level} {C : UU l4} {C' : UU l4'} →
    (c : cone-inverse-sequential-diagram A C)
    (c' : cone-inverse-sequential-diagram A' C') →
    is-sequential-limit A c → is-sequential-limit A' c' →
    hom-inverse-sequential-diagram A' A → C' → C
  map-hom-is-sequential-limit c c' is-lim-c is-lim-c' h x =
    map-inv-is-equiv
      ( is-lim-c)
      ( map-hom-standard-sequential-limit h
        ( gap-inverse-sequential-diagram A' c' x))
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
