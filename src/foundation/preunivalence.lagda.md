# The preunivalence axiom

```agda
module foundation.preunivalence where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.sets
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.subtypes
```

</details>

## Idea

**The preunivalence axiom**, or **axiom L**, which is due to Peter Lumsdaine,
asserts that for any two types `X` and `Y` in a common universe, the map
`X ＝ Y → X ≃ Y` is an [embedding](foundation-core.embeddings.md). This axiom is
a common generalization of the [univalence axiom](foundation.univalence.md) and
[axiom K](foundation-core.sets.md).

## Definition

```agda
instance-preunivalence : {l : Level} (X Y : UU l) → UU (lsuc l)
instance-preunivalence X Y = is-emb (equiv-eq {A = X} {B = Y})

based-preunivalence-axiom : {l : Level} (X : UU l) → UU (lsuc l)
based-preunivalence-axiom {l} X = (Y : UU l) → instance-preunivalence X Y

preunivalence-axiom-Level : (l : Level) → UU (lsuc l)
preunivalence-axiom-Level l = (X Y : UU l) → instance-preunivalence X Y

preunivalence-axiom : UUω
preunivalence-axiom = {l : Level} → preunivalence-axiom-Level l

emb-preunivalence :
  preunivalence-axiom → {l : Level} (X Y : UU l) → (X ＝ Y) ↪ (X ≃ Y)
pr1 (emb-preunivalence L X Y) = equiv-eq
pr2 (emb-preunivalence L X Y) = L X Y

emb-map-preunivalence :
  preunivalence-axiom → {l : Level} (X Y : UU l) → (X ＝ Y) ↪ (X → Y)
emb-map-preunivalence L X Y =
  comp-emb (emb-subtype is-equiv-Prop) (emb-preunivalence L X Y)
```

## Properties

### Preunivalence generalizes axiom K

To show that preunivalence generalizes axiom K, we assume axiom K for the types
in question and for the universe itself.

```agda
module _
  {l : Level} (A B : UU l)
  where

  instance-preunivalence-instance-axiom-K :
    instance-axiom-K (UU l) → instance-axiom-K A → instance-axiom-K B →
    instance-preunivalence A B
  instance-preunivalence-instance-axiom-K K-Type K-A K-B =
    is-emb-is-prop-is-set
      ( is-set-axiom-K K-Type A B)
      ( is-set-equiv-is-set (is-set-axiom-K K-A) (is-set-axiom-K K-B))

preunivalence-axiom-axiom-K : axiom-K → preunivalence-axiom
preunivalence-axiom-axiom-K K {l} X Y =
  instance-preunivalence-instance-axiom-K X Y (K (UU l)) (K X) (K Y)
```

### Preunivalence generalizes univalence

```agda
module _
  {l : Level} (A B : UU l)
  where

  instance-preunivalence-instance-univalence :
    instance-univalence A B → instance-preunivalence A B
  instance-preunivalence-instance-univalence = is-emb-is-equiv

preunivalence-axiom-univalence-axiom : univalence-axiom → preunivalence-axiom
preunivalence-axiom-univalence-axiom UA X Y =
  instance-preunivalence-instance-univalence X Y (UA X Y)
```

### Preunivalence holds in univalent foundations

```agda
preunivalence : preunivalence-axiom
preunivalence = preunivalence-axiom-univalence-axiom univalence
```

## See also

- Preunivalence is sufficient to prove that `Id : A → (A → 𝒰)` is an embedding.
  This fact is proven in
  [`foundation.universal-property-identity-types`](foundation.universal-property-identity-types.md)
- [The strong preunivalence axiom](foundation.strong-preunivalence.md)
- [Preunivalent type families](foundation.preunivalent-type-families.md)
- [Preunivalent categories](category-theory.preunivalent-categories.md)
