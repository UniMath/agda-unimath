# The poset of ideals in a commutative ring

```agda
module commutative-algebra.poset-of-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings

open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-preorders

open import ring-theory.poset-of-ideals-rings
```

</details>

## Idea

The **[large poset](order-theory.large-posets.md) of
[ideals](commutative-algebra.ideals-commutative-rings.md)** in a
[commutative ring](commutative-algebra.commutative-rings.md) `A` consists of
ideals in `A` and is ordered by inclusion.

## Definition

### The inclusion relation on ideals in a commutative ring

```agda
module _
  {l1 : Level} (A : Commutative-Ring l1)
  where

  leq-prop-ideal-Commutative-Ring :
    {l2 l3 : Level}
    (I : ideal-Commutative-Ring l2 A) (J : ideal-Commutative-Ring l3 A) →
    Prop (l1 ⊔ l2 ⊔ l3)
  leq-prop-ideal-Commutative-Ring =
    leq-prop-ideal-Ring (ring-Commutative-Ring A)

  leq-ideal-Commutative-Ring :
    {l2 l3 : Level}
    (I : ideal-Commutative-Ring l2 A) (J : ideal-Commutative-Ring l3 A) →
    UU (l1 ⊔ l2 ⊔ l3)
  leq-ideal-Commutative-Ring =
    leq-ideal-Ring (ring-Commutative-Ring A)

  is-prop-leq-ideal-Commutative-Ring :
    {l2 l3 : Level}
    (I : ideal-Commutative-Ring l2 A) (J : ideal-Commutative-Ring l3 A) →
    is-prop (leq-ideal-Commutative-Ring I J)
  is-prop-leq-ideal-Commutative-Ring =
    is-prop-leq-ideal-Ring (ring-Commutative-Ring A)

  refl-leq-ideal-Commutative-Ring :
    {l2 : Level}
    (I : ideal-Commutative-Ring l2 A) → leq-ideal-Commutative-Ring I I
  refl-leq-ideal-Commutative-Ring =
    refl-leq-ideal-Ring (ring-Commutative-Ring A)

  transitive-leq-ideal-Commutative-Ring :
    {l2 l3 l4 : Level}
    (I : ideal-Commutative-Ring l2 A)
    (J : ideal-Commutative-Ring l3 A)
    (K : ideal-Commutative-Ring l4 A) →
    leq-ideal-Commutative-Ring J K →
    leq-ideal-Commutative-Ring I J →
    leq-ideal-Commutative-Ring I K
  transitive-leq-ideal-Commutative-Ring =
    transitive-leq-ideal-Ring (ring-Commutative-Ring A)

  antisymmetric-leq-ideal-Commutative-Ring :
    {l2 : Level} (I J : ideal-Commutative-Ring l2 A) →
    leq-ideal-Commutative-Ring I J → leq-ideal-Commutative-Ring J I → I ＝ J
  antisymmetric-leq-ideal-Commutative-Ring =
    antisymmetric-leq-ideal-Ring (ring-Commutative-Ring A)
```

### The large preorder of ideals in a commutative ring

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  ideal-Commutative-Ring-Large-Preorder :
    Large-Preorder (λ l1 → l ⊔ lsuc l1) (λ l1 l2 → l ⊔ l1 ⊔ l2)
  type-Large-Preorder ideal-Commutative-Ring-Large-Preorder l1 =
    ideal-Commutative-Ring l1 A
  leq-prop-Large-Preorder ideal-Commutative-Ring-Large-Preorder =
    leq-prop-ideal-Commutative-Ring A
  refl-leq-Large-Preorder ideal-Commutative-Ring-Large-Preorder =
    refl-leq-ideal-Commutative-Ring A
  transitive-leq-Large-Preorder ideal-Commutative-Ring-Large-Preorder =
    transitive-leq-ideal-Commutative-Ring A
```

### The large poset of ideals in a commutative ring

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  ideal-Commutative-Ring-Large-Poset :
    Large-Poset (λ l1 → l ⊔ lsuc l1) (λ l1 l2 → l ⊔ l1 ⊔ l2)
  large-preorder-Large-Poset ideal-Commutative-Ring-Large-Poset =
    ideal-Commutative-Ring-Large-Preorder A
  antisymmetric-leq-Large-Poset ideal-Commutative-Ring-Large-Poset =
    antisymmetric-leq-ideal-Commutative-Ring A
```

### The similarity relation on ideals in a commutative ring

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  sim-prop-ideal-Commutative-Ring :
    {l1 l2 : Level}
    (I : ideal-Commutative-Ring l1 A) (J : ideal-Commutative-Ring l2 A) →
    Prop (l ⊔ l1 ⊔ l2)
  sim-prop-ideal-Commutative-Ring =
    sim-prop-ideal-Ring (ring-Commutative-Ring A)

  sim-ideal-Commutative-Ring :
    {l1 l2 : Level}
    (I : ideal-Commutative-Ring l1 A) (J : ideal-Commutative-Ring l2 A) →
    UU (l ⊔ l1 ⊔ l2)
  sim-ideal-Commutative-Ring =
    sim-ideal-Ring (ring-Commutative-Ring A)

  is-prop-sim-ideal-Commutative-Ring :
    {l1 l2 : Level}
    (I : ideal-Commutative-Ring l1 A) (J : ideal-Commutative-Ring l2 A) →
    is-prop (sim-ideal-Commutative-Ring I J)
  is-prop-sim-ideal-Commutative-Ring =
    is-prop-sim-ideal-Ring (ring-Commutative-Ring A)

  eq-sim-ideal-Commutative-Ring :
    {l1 : Level} (I J : ideal-Commutative-Ring l1 A) →
    sim-ideal-Commutative-Ring I J → I ＝ J
  eq-sim-ideal-Commutative-Ring =
    eq-sim-ideal-Ring (ring-Commutative-Ring A)
```
