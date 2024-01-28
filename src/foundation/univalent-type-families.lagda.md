# Univalent type families

```agda
module foundation.univalent-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.transport-split-type-families
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.identity-types
open import foundation-core.sections
```

</details>

## Idea

A type family `B` over `A` is said to be
{{#concept "univalent" Disambiguation="type family" Agda=is-univalent}} if the
map

```text
  equiv-tr : x ＝ y → B x ≃ B y
```

is an [equivalence](foundation-core.equivalences.md) for every `x y : A`. By
[univalence](foundation-core.univalence.md), this is equivalent to the type
family `B` being an [embedding](foundation-core.embeddings.md) considered as a
map.

## Definition

### The predicate on type families of being univalent

```agda
is-univalent :
  {l1 l2 : Level} {A : UU l1} → (A → UU l2) → UU (l1 ⊔ l2)
is-univalent {A = A} B = (x y : A) → is-equiv (λ (p : x ＝ y) → equiv-tr B p)

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-prop-is-univalent : is-prop (is-univalent B)
  is-prop-is-univalent =
    is-prop-iterated-Π 2 (λ x y → is-property-is-equiv (equiv-tr B))

  is-univalent-Prop : Prop (l1 ⊔ l2)
  pr1 is-univalent-Prop = is-univalent B
  pr2 is-univalent-Prop = is-prop-is-univalent
```

### Univalent type families

```agda
univalent-type-family :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
univalent-type-family l2 A = Σ (A → UU l2) is-univalent
```

## Properties

### Univalent type families are embeddings as maps

**Proof:** We have the
[commuting triangle of maps](foundation-core.commuting-triangles-of-maps.md)

```text
                ap B
       (x ＝ y) -----> (B x ＝ B y)
           \               /
            \             /
  equiv-tr B \           / equiv-eq
              v         v
              (B x ≃ B y)
```

where the right edge is an equivalence by the univalence axiom. Hence, the top
map is an equivalence if and only if the left map is.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    is-emb-is-univalent :
      is-univalent B → is-emb B
    is-emb-is-univalent U x y =
      is-equiv-top-map-triangle
        ( equiv-tr B)
        ( equiv-eq)
        ( ap B)
        ( λ where refl → refl)
        ( univalence (B x) (B y))
        ( U x y)

    is-univalent-is-emb :
      is-emb B → is-univalent B
    is-univalent-is-emb is-emb-B x y =
      is-equiv-left-map-triangle
        ( equiv-tr B)
        ( equiv-eq)
        ( ap B)
        ( λ where refl → refl)
        ( is-emb-B x y)
        ( univalence (B x) (B y))
```

### Univalent type families are transport-split

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-transport-split-is-univalent :
    is-univalent B → is-transport-split B
  is-transport-split-is-univalent U x y = section-is-equiv (U x y)
```

### Univalent type families satisfy an equivalence induction principle

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (U : is-univalent B)
  {P : {x y : A} → B x ≃ B y → UU l3}
  where

  ind-equiv-is-univalent' :
    (f : {x y : A} (p : x ＝ y) → P (equiv-tr B p))
    {x y : A} (e : B x ≃ B y) → P e
  ind-equiv-is-univalent' =
    ind-equiv-is-transport-split' (is-transport-split-is-univalent U)
```

## See also

- [Univalent type families](foundation.univalent-type-families.md)
- [Preunivalent type families](foundation.preunivalent-type-families.md)
- [Transport-split type families](foundation.transport-split-type-families.md)
