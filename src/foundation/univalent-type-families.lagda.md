# Univalent type families

```agda
module foundation.univalent-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.global-subuniverses
open import foundation.identity-systems
open import foundation.iterated-dependent-product-types
open import foundation.monomorphisms
open import foundation.propositions
open import foundation.retractions
open import foundation.subtype-identity-principle
open import foundation.subuniverses
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universal-property-identity-systems
open import foundation.universe-levels

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
univalent-family :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
univalent-family l2 A = Σ (A → UU l2) is-univalent

module _
  {l1 l2 : Level} {A : UU l1} (ℬ : univalent-family l2 A)
  where

  type-family-univalent-family : A → UU l2
  type-family-univalent-family = pr1 ℬ

  is-univalent-univalent-family :
    is-univalent type-family-univalent-family
  is-univalent-univalent-family =
    pr2 ℬ

  equiv-equiv-tr-univalent-family :
    {x y : A} →
    ( x ＝ y) ≃
    ( type-family-univalent-family x ≃ type-family-univalent-family y)
  equiv-equiv-tr-univalent-family {x} {y} =
    ( equiv-tr type-family-univalent-family ,
      is-univalent-univalent-family x y)
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
map is an equivalence if and only if the left map is. ∎

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

emb-univalent-family :
  {l1 l2 : Level} {A : UU l1} → univalent-family l2 A → A ↪ UU l2
emb-univalent-family (B , H) = (B , is-emb-is-univalent H)
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

### The underlying global subuniverse of a univalent type family

```agda
module _
  {l1 l2 : Level} {A : UU l1} ((B , H) : univalent-family l2 A)
  where

  is-in-subuniverse-univalent-family : {l3 : Level} → UU l3 → UU (l1 ⊔ l2 ⊔ l3)
  is-in-subuniverse-univalent-family X = Σ A (λ a → (B a ≃ X))

  abstract
    is-prop-is-in-subuniverse-univalent-family :
      {l3 : Level} {X : UU l3} → is-prop (is-in-subuniverse-univalent-family X)
    is-prop-is-in-subuniverse-univalent-family {X = X} =
      is-prop-emb
        ( emb-Σ-emb-base (emb-univalent-family (B , H)) (λ Y → Y ≃ X))
        ( is-prop-is-proof-irrelevant
          ( λ (Y , e) →
            is-contr-equiv'
              ( Σ (UU l2) (λ Y' → Y' ≃ Y))
              ( equiv-tot (equiv-postcomp-equiv e))
              ( is-torsorial-equiv' Y)))

  is-in-subuniverse-prop-univalent-family :
    {l3 : Level} → UU l3 → Prop (l1 ⊔ l2 ⊔ l3)
  is-in-subuniverse-prop-univalent-family X =
    ( is-in-subuniverse-univalent-family X ,
      is-prop-is-in-subuniverse-univalent-family)

  subuniverse-univalent-family : (l3 : Level) → subuniverse l3 (l1 ⊔ l2 ⊔ l3)
  subuniverse-univalent-family l3 = is-in-subuniverse-prop-univalent-family

  is-closed-under-equiv-subuniverse-univalent-family :
    {l3 l4 : Level} →
    is-closed-under-equiv-subuniverses
      (λ l → l1 ⊔ l2 ⊔ l) subuniverse-univalent-family l3 l4
  is-closed-under-equiv-subuniverse-univalent-family X Y f (a , e) =
    ( a , f ∘e e)

  global-subuniverse-univalent-family :
    global-subuniverse (λ l → l1 ⊔ l2 ⊔ l)
  global-subuniverse-univalent-family =
    λ where
      .subuniverse-global-subuniverse →
        subuniverse-univalent-family
      .is-closed-under-equiv-global-subuniverse →
        is-closed-under-equiv-subuniverse-univalent-family
```

### The indexing type of a univalent type family is equivalent to the subuniverse

```agda
module _
  {l1 l2 : Level} {A : UU l1} (ℬ : univalent-family l2 A)
  where

  map-equiv-type-subuniverse-univalent-family :
    A → type-subuniverse (subuniverse-univalent-family ℬ l2)
  map-equiv-type-subuniverse-univalent-family a =
    (type-family-univalent-family ℬ a , a , id-equiv)

  map-inv-equiv-type-subuniverse-univalent-family :
     type-subuniverse (subuniverse-univalent-family ℬ l2) → A
  map-inv-equiv-type-subuniverse-univalent-family (X , a , e) = a

  is-retraction-map-inv-equiv-type-subuniverse-univalent-family :
    is-retraction
      map-equiv-type-subuniverse-univalent-family
      map-inv-equiv-type-subuniverse-univalent-family
  is-retraction-map-inv-equiv-type-subuniverse-univalent-family a = refl

  is-section-map-inv-equiv-type-subuniverse-univalent-family :
    is-section
      map-equiv-type-subuniverse-univalent-family
      map-inv-equiv-type-subuniverse-univalent-family
  is-section-map-inv-equiv-type-subuniverse-univalent-family (X , a , e) =
    eq-equiv-subuniverse (subuniverse-univalent-family ℬ l2) e

  is-equiv-map-equiv-type-subuniverse-univalent-family :
    is-equiv map-equiv-type-subuniverse-univalent-family
  is-equiv-map-equiv-type-subuniverse-univalent-family =
    is-equiv-is-invertible
      map-inv-equiv-type-subuniverse-univalent-family
      is-section-map-inv-equiv-type-subuniverse-univalent-family
      is-retraction-map-inv-equiv-type-subuniverse-univalent-family

  is-equiv-map-inv-equiv-type-subuniverse-univalent-family :
    is-equiv map-inv-equiv-type-subuniverse-univalent-family
  is-equiv-map-inv-equiv-type-subuniverse-univalent-family =
    is-equiv-is-invertible
      map-equiv-type-subuniverse-univalent-family
      is-retraction-map-inv-equiv-type-subuniverse-univalent-family
      is-section-map-inv-equiv-type-subuniverse-univalent-family

  equiv-type-subuniverse-univalent-family :
    A ≃ type-subuniverse (subuniverse-univalent-family ℬ l2)
  equiv-type-subuniverse-univalent-family =
    ( map-equiv-type-subuniverse-univalent-family ,
      is-equiv-map-equiv-type-subuniverse-univalent-family)

  inv-equiv-type-subuniverse-univalent-family :
    type-subuniverse (subuniverse-univalent-family ℬ l2) ≃ A
  inv-equiv-type-subuniverse-univalent-family =
    ( map-inv-equiv-type-subuniverse-univalent-family ,
      is-equiv-map-inv-equiv-type-subuniverse-univalent-family)
```

## See also

- [Preunivalent type families](foundation.preunivalent-type-families.md)
- [Transport-split type families](foundation.transport-split-type-families.md):
  By a corollary of
  [the fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md),
  `equiv-tr B` is a
  [fiberwise equivalence](foundation-core.families-of-equivalences.md) as soon
  as it admits a fiberwise [section](foundation-core.sections.md).
