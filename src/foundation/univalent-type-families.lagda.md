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
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-systems
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.subuniverses
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universal-property-identity-systems
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.sections
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A type family `B` over `A` is said to be
{{#concept "univalent" Disambiguation="type family" Agda=is-univalent}} if the
map

```text
  equiv-tr B : x ＝ y → B x ≃ B y
```

is an [equivalence](foundation-core.equivalences.md) for every `x y : A`. By
[the univalence axiom](foundation-core.univalence.md), this is equivalent to the
type family `B` being an [embedding](foundation-core.embeddings.md) considered
as a map. In other words, that `A` is a
[subuniverse](foundation.subuniverses.md).

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

### The univalence axiom states that the identity family `id : 𝒰 → 𝒰` is univalent

```agda
is-univalent-UU :
  (l : Level) → is-univalent (id {A = UU l})
is-univalent-UU l = univalence
```

### Assuming the univalence axiom, type families are univalent if and only if they are embeddings as maps

**Proof:** We have the
[commuting triangle of maps](foundation-core.commuting-triangles-of-maps.md)

```text
                ap B
       (x ＝ y) -----> (B x ＝ B y)
           \               /
            \             /
  equiv-tr B \           / equiv-eq
              ∨         ∨
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

### Univalent type families satisfy equivalence induction

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (U : is-univalent B)
  where

  is-torsorial-fam-equiv-is-univalent :
    {x : A} → is-torsorial (λ y → B x ≃ B y)
  is-torsorial-fam-equiv-is-univalent {x} =
    fundamental-theorem-id' (λ y → equiv-tr B) (U x)

  dependent-universal-property-identity-system-fam-equiv-is-univalent :
    {x : A} →
    dependent-universal-property-identity-system (λ y → B x ≃ B y) id-equiv
  dependent-universal-property-identity-system-fam-equiv-is-univalent {x} =
    dependent-universal-property-identity-system-is-torsorial
      ( id-equiv)
      ( is-torsorial-fam-equiv-is-univalent {x})
```

### Inclusions of subuniverses into the universe are univalent

**Note.** This proof relies on essential use of the univalence axiom.

```agda
module _
  {l1 l2 : Level} (S : subuniverse l1 l2)
  where

  is-univalent-inclusion-subuniverse : is-univalent (inclusion-subuniverse S)
  is-univalent-inclusion-subuniverse =
    is-univalent-is-emb (is-emb-inclusion-subuniverse S)
```

## See also

- [Preunivalent type families](foundation.preunivalent-type-families.md)
- [Transport-split type families](foundation.transport-split-type-families.md):
  By a corollary of
  [the fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md),
  `equiv-tr B` is a
  [fiberwise equivalence](foundation-core.families-of-equivalences.md) as soon
  as it admits a fiberwise [section](foundation-core.sections.md).
