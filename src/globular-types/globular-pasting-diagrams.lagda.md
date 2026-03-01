# Globular pasting diagrams

```agda
{-# OPTIONS --guardedness #-}

module globular-types.globular-pasting-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import globular-types.globular-maps
open import globular-types.globular-pasting-schemes
open import globular-types.globular-types

open import trees.plane-trees
```

</details>

## Idea

A
{{#concept "globular pasting diamgram" Disambiguation="globular types" Agda=pasting-diagram-Globular-Type}}
in a [globular type](globular-types.globular-types.md) `G` is a
[globular map](globular-types.globular-maps.md) from a
[globular pasting scheme](globular-types.globular-pasting-schemes.md) into `G`.

## Definitions

### Globular pasting diagrams

```agda
module _
  {l1 l2 : Level} (T : listed-plane-tree) (G : Globular-Type l1 l2)
  where

  pasting-diagram-Globular-Type : UU (l1 ⊔ l2)
  pasting-diagram-Globular-Type =
    globular-map (pasting-scheme-Globular-Type T) G
```
