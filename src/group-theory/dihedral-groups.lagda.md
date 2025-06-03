# The dihedral groups

```agda
module group-theory.dihedral-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.standard-cyclic-groups

open import foundation.universe-levels

open import group-theory.dihedral-group-construction
open import group-theory.groups
```

</details>

## Idea

The dihedral group `Dₖ` is defined by the dihedral group construction applied to
the cyclic group `ℤ-Mod k`.

## Definition

```agda
dihedral-group : ℕ → Group lzero
dihedral-group k = dihedral-group-Ab (ℤ-Mod-Ab k)
```
