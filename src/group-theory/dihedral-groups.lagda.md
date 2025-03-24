# The dihedral groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.dihedral-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.standard-cyclic-groups funext univalence truncations

open import foundation.universe-levels

open import group-theory.dihedral-group-construction funext univalence truncations
open import group-theory.groups funext univalence truncations
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
