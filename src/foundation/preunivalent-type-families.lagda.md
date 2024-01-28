# Preunivalent type families

```agda
module foundation.preunivalent-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.identity-types
```

</details>

## Idea

A type family `B` over `A` is said to be
{{#concept "preunivalent" Disambiguation="type family" Agda=is-preunivalent}} if
the map

```text
  equiv-tr : x ＝ y → B x ≃ B y
```

is an [embedding](foundation-core.embeddings.md) for every `x y : A`.

## Definition

```agda
is-preunivalent :
  {l1 l2 : Level} {A : UU l1} → (A → UU l2) → UU (l1 ⊔ l2)
is-preunivalent {A = A} B = (x y : A) → is-emb (λ (p : x ＝ y) → equiv-tr B p)
```

## See also

- [Univalent type families](foundation.univalent-type-families.md)
- [Transport-split type families](foundation.transport-split-type-families.md)
