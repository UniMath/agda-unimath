# Discrete dependent reflexive globular types

```agda
{-# OPTIONS --guardedness #-}
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module globular-types.discrete-dependent-reflexive-globular-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import globular-types.dependent-reflexive-globular-types funext univalence truncations
open import globular-types.discrete-reflexive-globular-types funext univalence truncations
open import globular-types.points-reflexive-globular-types funext univalence truncations
open import globular-types.reflexive-globular-types funext univalence truncations
```

</details>

## Idea

A
[dependent reflexive globular type](globular-types.dependent-reflexive-globular-types.md)
`H` over a [reflexive globular type](globular-types.reflexive-globular-types.md)
`G` is said to be
{{#concept "discrete" Disambiguation="dependent reflexive globular type" Agda=is-discrete-Dependent-Reflexive-Globular-Type}}
if the reflexive globular type

```text
  ev-point H x
```

is [discrete](globular-types.discrete-reflexive-globular-types.md) for every
[point](globular-types.points-reflexive-globular-types.md) of `G`.

## Definitions

### The predicate of being a discrete dependent reflexive globular type

```agda
module _
  {l1 l2 l3 l4 : Level} {G : Reflexive-Globular-Type l1 l2}
  (H : Dependent-Reflexive-Globular-Type l3 l4 G)
  where

  is-discrete-Dependent-Reflexive-Globular-Type : UU (l1 ⊔ l3 ⊔ l4)
  is-discrete-Dependent-Reflexive-Globular-Type =
    (x : point-Reflexive-Globular-Type G) →
    is-discrete-Reflexive-Globular-Type
      ( ev-point-Dependent-Reflexive-Globular-Type H x)
```
