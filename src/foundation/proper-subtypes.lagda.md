# Proper subsets

```agda
open import foundation.function-extensionality-axiom

module
  foundation.proper-subtypes
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.complements-subtypes funext
open import foundation.inhabited-subtypes funext
open import foundation.universe-levels

open import foundation-core.propositions
open import foundation-core.subtypes funext
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
