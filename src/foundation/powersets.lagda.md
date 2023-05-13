# Powersets

```agda
module foundation.powersets where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality
open import foundation.propositional-extensionality
open import foundation.subtypes

open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.universe-levels

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Definition

```agda
powerset :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
powerset = subtype
```

## Properties

### The powerset preorder and poset

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  powerset-Large-Preorder :
    Large-Preorder (λ l → l1 ⊔ lsuc l) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  type-Large-Preorder powerset-Large-Preorder l = subtype l A
  leq-Large-Preorder-Prop powerset-Large-Preorder = leq-subtype-Prop
  refl-leq-Large-Preorder powerset-Large-Preorder = refl-leq-subtype
  transitive-leq-Large-Preorder powerset-Large-Preorder = transitive-leq-subtype

  powerset-Preorder : (l2 : Level) → Preorder (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  powerset-Preorder = preorder-Large-Preorder powerset-Large-Preorder

  powerset-Large-Poset :
    Large-Poset (λ l → l1 ⊔ lsuc l) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  large-preorder-Large-Poset powerset-Large-Poset = powerset-Large-Preorder
  antisymmetric-leq-Large-Poset powerset-Large-Poset P Q =
    antisymmetric-leq-subtype P Q

  powerset-Poset : (l2 : Level) → Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  powerset-Poset = poset-Large-Poset powerset-Large-Poset
```
