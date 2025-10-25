# Species of finite inhabited types

```agda
module species.species-of-finite-inhabited-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import species.species-of-types-in-subuniverses

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
```

</details>

## Idea

A
{{#concept "species of finite inhabited types" Agda=species-Inhabited-Finite-Type}}
is a map from the [subuniverse](foundation.global-subuniverses.md) of
[finite inhabited types](univalent-combinatorics.inhabited-finite-types.md) to
the universe of [finite types](univalent-combinatorics.finite-types.md).

## Definition

```agda
species-Inhabited-Finite-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
species-Inhabited-Finite-Type l1 l2 =
  species-subuniverse (is-finite-and-inhabited-Prop {l1}) (is-finite-Prop {l2})
```
