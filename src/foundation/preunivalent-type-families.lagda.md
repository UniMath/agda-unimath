# Preunivalent type families

```agda
module foundation.preunivalent-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.embeddings
open import foundation.equivalence-injective-type-families
open import foundation.faithful-maps
open import foundation.preunivalence
open import foundation.retractions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.sets
open import foundation-core.univalence
```

</details>

## Idea

A type family `B` over `A` is said to be
{{#concept "preunivalent" Disambiguation="type family" Agda=is-preunivalent}} if
the map

```text
  equiv-tr B : x ＝ y → B x ≃ B y
```

is an [embedding](foundation-core.embeddings.md) for every `x y : A`.

## Definition

```agda
is-preunivalent :
  {l1 l2 : Level} {A : UU l1} → (A → UU l2) → UU (l1 ⊔ l2)
is-preunivalent {A = A} B = (x y : A) → is-emb (λ (p : x ＝ y) → equiv-tr B p)
```

## Properties

### Type families are preunivalent if and only if they are faithful as maps

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
```

### Families of sets are preunivalent if `equiv-tr` is fiberwise injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  (is-set-B : (x : A) → is-set (B x))
  where

  is-preunivalent-is-injective-equiv-tr :
    ((x y : A) → is-injective (equiv-tr B {x} {y})) →
    is-preunivalent B
  is-preunivalent-is-injective-equiv-tr is-inj-B x y =
    is-emb-is-injective
      ( is-set-equiv-is-set (is-set-B x) (is-set-B y))
      ( is-inj-B x y)

  is-preunivalent-retraction-equiv-tr :
    ((x y : A) → retraction (equiv-tr B {x} {y})) →
    is-preunivalent B
  is-preunivalent-retraction-equiv-tr R =
    is-preunivalent-is-injective-equiv-tr
      ( λ x y → is-injective-retraction (equiv-tr B) (R x y))
```

## See also

- [Univalent type families](foundation.univalent-type-families.md)
- [Transport-split type families](foundation.transport-split-type-families.md)
