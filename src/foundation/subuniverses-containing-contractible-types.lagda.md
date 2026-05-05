# Subuniverses containing contractible types

```agda
module foundation.subuniverses-containing-contractible-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.subuniverses
```

</details>

## Idea

We define the predicate on [subuniverses](foundation-core.subuniverses.md) that
they contain a contractible type.

## Definitions

### The predicate that a subuniverse contains any contractible types

```agda
contains-contractible-types-subuniverse :
  {l1 l2 : Level} → subuniverse l1 l2 → UU (lsuc l1 ⊔ l2)
contains-contractible-types-subuniverse {l1} P =
  (X : UU l1) → is-contr X → is-in-subuniverse P X
```

### The predicate that a subuniverse is closed under the `is-contr` predicate

We state a general form involving two universes, and a more traditional form
using a single universe

```agda
is-closed-under-is-contr-subuniverses :
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (Q : subuniverse l1 l3) →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
is-closed-under-is-contr-subuniverses P Q =
  (X : type-subuniverse P) →
  is-in-subuniverse Q (is-contr (inclusion-subuniverse P X))

is-closed-under-is-contr-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU (lsuc l1 ⊔ l2)
is-closed-under-is-contr-subuniverse P =
  is-closed-under-is-contr-subuniverses P P
```
