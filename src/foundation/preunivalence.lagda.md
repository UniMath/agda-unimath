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
open import foundation.subtypes
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.univalence
```

</details>

## Idea

**The preunivalence axiom**, or **axiom L**, which is due to Peter Lumsdaine,
asserts that for any two types `X` and `Y` in a common universe, the map
`X ＝ Y → X ≃ Y` is an [embedding](foundation-core.embeddings.md). This axiom is
a common generalization of the [univalence axiom](foundation.univalence.md) and
[axiom K](foundation-core.sets.md), in the sense that both univalence and axiom
K imply preunivalence.

## Definition

```agda
statement-preunivalence : {l : Level} (X Y : UU l) → UU (lsuc l)
statement-preunivalence X Y = is-emb (equiv-eq {A = X} {B = Y})

axiom-preunivalence : (l : Level) → UU (lsuc l)
axiom-preunivalence l = (X Y : UU l) → statement-preunivalence X Y

emb-preunivalence :
  {l : Level} → axiom-preunivalence l → (X Y : UU l) → (X ＝ Y) ↪ (X ≃ Y)
pr1 (emb-preunivalence preuniv X Y) = equiv-eq
pr2 (emb-preunivalence preuniv X Y) = preuniv X Y

emb-map-preunivalence :
  {l : Level} → axiom-preunivalence l → (X Y : UU l) → (X ＝ Y) ↪ (X → Y)
emb-map-preunivalence preuniv X Y =
  comp-emb (emb-subtype is-equiv-Prop) (emb-preunivalence preuniv X Y)
```

## Properties

### Preunivalence generalizes univalence

```agda
preunivalence-univalence :
  {l : Level} → axiom-univalence l → axiom-preunivalence l
preunivalence-univalence ua A B = is-emb-is-equiv (ua A B)
```

### Preunivalence generalizes axiom K

To show that preunivalence generalizes axiom K, we assume axiom K both for
types, and for the universe itself.

```agda
preunivalence-axiom-K :
  {l : Level} → axiom-K l → statement-axiom-K (UU l) → axiom-preunivalence l
preunivalence-axiom-K K K-Type A B =
  is-emb-is-prop-is-set
    ( is-set-axiom-K K-Type A B)
    ( is-set-equiv-is-set
      ( is-set-axiom-K (K A))
      ( is-set-axiom-K (K B)))
```

## See also

- Preunivalence is sufficient to prove that `Id : A → (A → 𝒰)` is an embedding.
  This fact is proven in
  [`foundation.universal-property-identity-types`](foundation.universal-property-identity-types.md)
