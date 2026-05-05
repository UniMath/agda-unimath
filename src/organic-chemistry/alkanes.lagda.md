# Alkanes

```agda
module organic-chemistry.alkanes where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import organic-chemistry.hydrocarbons
open import organic-chemistry.saturated-carbons
```

</details>

## Idea

An {{#concept "alkane" WD="alkane" WDID=Q41581 Agda=is-alkane-hydrocarbon}} is a
[hydrocarbon](organic-chemistry.hydrocarbons.md) that only has
[saturated carbons](organic-chemistry.saturated-carbons.md), i.e., it does not
have any double or triple carbon-carbon bonds.

## Definition

```agda
is-alkane-hydrocarbon : {l1 l2 : Level} → hydrocarbon l1 l2 → UU (l1 ⊔ l2)
is-alkane-hydrocarbon H =
  (c : vertex-hydrocarbon H) → is-saturated-carbon-hydrocarbon H c
```
