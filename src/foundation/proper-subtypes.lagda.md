# Proper subsets

```agda
module foundation.proper-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.complements-subtypes
open import foundation.inhabited-subtypes
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A subtype of a type is said to be **proper** if its complement is inhabited.

```agda
is-proper-subtype-Prop :
  {l1 l2 : Level} {A : UU l1} → subtype l2 A → Prop (l1 ⊔ l2)
is-proper-subtype-Prop P =
  is-inhabited-subtype-Prop (complement-subtype P)
```
