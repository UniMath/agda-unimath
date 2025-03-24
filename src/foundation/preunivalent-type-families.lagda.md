# Preunivalent type families

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.preunivalent-type-families
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-maps funext
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings funext
open import foundation.equivalence-injective-type-families funext univalence
open import foundation.faithful-maps funext
open import foundation.function-types funext
open import foundation.injective-maps funext
open import foundation.preunivalence funext univalence
open import foundation.retractions funext
open import foundation.sets funext univalence
open import foundation.subuniverses funext univalence
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
```

</details>

## Idea

A type family `B` over `A` is said to be
{{#concept "preunivalent" Disambiguation="type family" Agda=is-preunivalent}} if
the map

```text
  equiv-tr B : x ＝ y → B x ≃ B y
```

is an [embedding](foundation-core.embeddings.md) for every `x y : A`. By
[the preunivalence axiom](foundation.preunivalence.md), which follows from
[the univalence axiom](foundation.univalence.md), the type family `B` is
preunivalent if and only if it is [faithful](foundation.faithful-maps.md) as a
map. In other words, if `A` is a [set](foundation-core.sets.md)-level
[structure](foundation.structure.md) on types.

## Definition

```agda
is-preunivalent :
  {l1 l2 : Level} {A : UU l1} → (A → UU l2) → UU (l1 ⊔ l2)
is-preunivalent {A = A} B = (x y : A) → is-emb (λ (p : x ＝ y) → equiv-tr B p)
```

## Properties

### The preunivalence axiom states that the identity family `id : 𝒰 → 𝒰` is preunivalent

```agda
is-preunivalent-UU :
  (l : Level) → is-preunivalent (id {A = UU l})
is-preunivalent-UU l = preunivalence
```

### Assuming the preunivalence axiom, type families are preunivalent if and only if they are faithful as maps

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

where the right edge is an embedding by the
[preunivalence axiom](foundation.preunivalence.md). Hence, the top map is an
embedding if and only if the left map is.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    is-faithful-is-preunivalent :
      is-preunivalent B → is-faithful B
    is-faithful-is-preunivalent U x y =
      is-emb-top-map-triangle
        ( equiv-tr B)
        ( equiv-eq)
        ( ap B)
        ( λ where refl → refl)
        ( preunivalence (B x) (B y))
        ( U x y)

    is-preunivalent-is-faithful :
      is-faithful B → is-preunivalent B
    is-preunivalent-is-faithful is-faithful-B x y =
      is-emb-left-map-triangle
        ( equiv-tr B)
        ( equiv-eq)
        ( ap B)
        ( λ where refl → refl)
        ( preunivalence (B x) (B y))
        ( is-faithful-B x y)

    is-0-map-is-preunivalent :
      is-preunivalent B → is-0-map B
    is-0-map-is-preunivalent U =
      is-0-map-is-faithful (is-faithful-is-preunivalent U)

    is-preunivalent-is-0-map :
      is-0-map B → is-preunivalent B
    is-preunivalent-is-0-map H =
      is-preunivalent-is-faithful (is-faithful-is-0-map H)
```

### Families of sets are preunivalent if `equiv-tr` is fiberwise injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  (is-set-B : (x : A) → is-set (B x))
  where

  is-preunivalent-is-injective-equiv-tr-is-set :
    ((x y : A) → is-injective (equiv-tr B {x} {y})) →
    is-preunivalent B
  is-preunivalent-is-injective-equiv-tr-is-set is-inj-B x y =
    is-emb-is-injective
      ( is-set-equiv-is-set (is-set-B x) (is-set-B y))
      ( is-inj-B x y)

  is-preunivalent-retraction-equiv-tr-is-set :
    ((x y : A) → retraction (equiv-tr B {x} {y})) →
    is-preunivalent B
  is-preunivalent-retraction-equiv-tr-is-set R =
    is-preunivalent-is-injective-equiv-tr-is-set
      ( λ x y → is-injective-retraction (equiv-tr B) (R x y))

module _
  {l1 l2 : Level} {A : UU l1} (B : A → Set l2)
  where

  is-preunivalent-is-injective-equiv-tr-Set :
    ((x y : A) → is-injective (equiv-tr (type-Set ∘ B) {x} {y})) →
    is-preunivalent (type-Set ∘ B)
  is-preunivalent-is-injective-equiv-tr-Set =
    is-preunivalent-is-injective-equiv-tr-is-set
      ( type-Set ∘ B)
      ( is-set-type-Set ∘ B)

  is-preunivalent-retraction-equiv-tr-Set :
    ((x y : A) → retraction (equiv-tr (type-Set ∘ B) {x} {y})) →
    is-preunivalent (type-Set ∘ B)
  is-preunivalent-retraction-equiv-tr-Set =
    is-preunivalent-retraction-equiv-tr-is-set
      ( type-Set ∘ B)
      ( is-set-type-Set ∘ B)
```

### Inclusions of subuniverses into the universe are preunivalent

**Note.** These proofs rely on essential use of the preunivalence axiom.

```agda
is-preunivalent-projection-Type-With-Set-Element :
  {l1 l2 : Level} (S : UU l1 → Set l2) →
  is-preunivalent (pr1 {A = UU l1} {B = type-Set ∘ S})
is-preunivalent-projection-Type-With-Set-Element S =
  is-preunivalent-is-0-map (is-0-map-pr1 (is-set-type-Set ∘ S))

is-preunivalent-inclusion-subuniverse :
  {l1 l2 : Level} (S : subuniverse l1 l2) →
  is-preunivalent (inclusion-subuniverse S)
is-preunivalent-inclusion-subuniverse S =
  is-preunivalent-projection-Type-With-Set-Element (set-Prop ∘ S)
```

## See also

- [Univalent type families](foundation.univalent-type-families.md)
- [Transport-split type families](foundation.transport-split-type-families.md)
- The [standard finite types](univalent-combinatorics.standard-finite-types.md)
  is a type family which is preunivalent but not univalent.
