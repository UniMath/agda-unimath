# Divisible groups

```agda
module group-theory.divisible-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.surjective-maps
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.powers-of-elements-groups
```

</details>

## Idea

A group `G` is called **divisible** if for every `n : ℕ⁺`, the
[power-of-`n` map](group-theory.powers-of-elements-groups.md)
`x ↦ power-Group G n x` is surjective.

## Definition

```agda
is-divisible-Group : {l : Level} (G : Group l) → UU l
is-divisible-Group G = (n : ℕ⁺) → is-surjective (power-Group G (nat-ℕ⁺ n))

is-prop-is-divisible-Group :
  {l : Level} (G : Group l) → is-prop (is-divisible-Group G)
is-prop-is-divisible-Group G =
  is-prop-Π λ n → is-prop-is-surjective (power-Group G (nat-ℕ⁺ n))

is-divisible-Group-Prop : {l : Level} (G : Group l) → Prop l
is-divisible-Group-Prop G = is-divisible-Group G , is-prop-is-divisible-Group G
```
