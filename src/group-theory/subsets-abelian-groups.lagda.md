# Subsets of abelian groups

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.subsets-abelian-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-locale-of-subtypes funext
open import foundation.powersets funext
open import foundation.sets funext
open import foundation.universe-levels

open import group-theory.abelian-groups funext
open import group-theory.subsets-groups funext

open import order-theory.large-locales funext
open import order-theory.large-posets funext
```

</details>

## Idea

A **subset** of an [abelian group](group-theory.abelian-groups.md) `A` is a
[subtype](foundation.subtypes.md) of the underlying type of `A`. The
[large poset](order-theory.large-posets.md) of all subsets of `A` is called the
**powerset** of `A`.

## Definitions

### The large locale of subsets of an abelian group

```agda
module _
  {l1 : Level} (G : Ab l1)
  where

  powerset-large-locale-Ab :
    Large-Locale (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3) lzero
  powerset-large-locale-Ab = powerset-Large-Locale (type-Ab G)
```

### The large poset of subsets of an abelian group

```agda
module _
  {l1 : Level} (G : Ab l1)
  where

  powerset-large-poset-Ab :
    Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  powerset-large-poset-Ab =
    large-poset-Large-Locale (powerset-large-locale-Ab G)
```

### Subsets of abelian groups

```agda
subset-Ab :
  (l : Level) {l1 : Level} (A : Ab l1) → UU (lsuc l ⊔ l1)
subset-Ab l A = subset-Group l (group-Ab A)

is-set-subset-Ab :
  (l : Level) {l1 : Level} (A : Ab l1) → is-set (subset-Ab l A)
is-set-subset-Ab l A = is-set-subset-Group (group-Ab A)
```
