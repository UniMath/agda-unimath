# Isomorphisms of abelian groups

```agda
module group-theory.isomorphisms-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.isomorphisms-groups
```

</details>

## Idea

**Isomorphisms** between [abelian groups](group-theory.abelian-groups.md) are
just [isomorphisms](group-theory.isomorphisms-groups.md) between their
underlying [groups](group-theory.groups.md).

## Definitions

### The predicate of being an isomorphism of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : hom-Ab A B)
  where

  is-iso-Ab : UU (l1 ⊔ l2)
  is-iso-Ab = is-iso-Group (group-Ab A) (group-Ab B) f

  is-prop-is-iso-Ab : is-prop is-iso-Ab
  is-prop-is-iso-Ab =
    is-prop-is-iso-Group (group-Ab A) (group-Ab B) f

  is-iso-prop-Ab : Prop (l1 ⊔ l2)
  is-iso-prop-Ab = is-iso-prop-Group (group-Ab A) (group-Ab B) f

  hom-inv-is-iso-Ab : is-iso-Ab → hom-Ab B A
  hom-inv-is-iso-Ab = hom-inv-is-iso-Group (group-Ab A) (group-Ab B) f

  map-inv-is-iso-Ab : is-iso-Ab → type-Ab B → type-Ab A
  map-inv-is-iso-Ab =
    map-inv-is-iso-Group (group-Ab A) (group-Ab B) f

  is-section-hom-inv-is-iso-Ab :
    (H : is-iso-Ab) →
    comp-hom-Ab B A B f (hom-inv-is-iso-Ab H) ＝ id-hom-Ab B
  is-section-hom-inv-is-iso-Ab =
    is-section-hom-inv-is-iso-Group (group-Ab A) (group-Ab B) f

  is-section-map-inv-is-iso-Ab :
    (H : is-iso-Ab) →
    ( map-hom-Ab A B f ∘ map-hom-Ab B A (hom-inv-is-iso-Ab H)) ~ id
  is-section-map-inv-is-iso-Ab =
    is-section-map-inv-is-iso-Group
      ( group-Ab A)
      ( group-Ab B)
      ( f)

  is-retraction-hom-inv-is-iso-Ab :
    (H : is-iso-Ab) →
    comp-hom-Ab A B A (hom-inv-is-iso-Ab H) f ＝ id-hom-Ab A
  is-retraction-hom-inv-is-iso-Ab H = pr2 (pr2 H)

  is-retraction-map-inv-is-iso-Ab :
    (H : is-iso-Ab) →
    ( map-inv-is-iso-Ab H ∘ map-hom-Ab A B f) ~ id
  is-retraction-map-inv-is-iso-Ab =
    is-retraction-map-inv-is-iso-Group
      ( group-Ab A)
      ( group-Ab B)
      ( f)
```

### The predicate of being an equivalence of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  is-equiv-hom-Ab : hom-Ab A B → UU (l1 ⊔ l2)
  is-equiv-hom-Ab =
    is-equiv-hom-Group (group-Ab A) (group-Ab B)

  equiv-Ab : UU (l1 ⊔ l2)
  equiv-Ab = equiv-Group (group-Ab A) (group-Ab B)
```

### The type of isomorphisms of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  iso-Ab : UU (l1 ⊔ l2)
  iso-Ab = iso-Group (group-Ab A) (group-Ab B)

  hom-iso-Ab : iso-Ab → hom-Ab A B
  hom-iso-Ab = hom-iso-Group (group-Ab A) (group-Ab B)

  map-iso-Ab : iso-Ab → type-Ab A → type-Ab B
  map-iso-Ab = map-iso-Group (group-Ab A) (group-Ab B)

  preserves-add-iso-Ab :
    (f : iso-Ab) {x y : type-Ab A} →
    map-iso-Ab f (add-Ab A x y) ＝ add-Ab B (map-iso-Ab f x) (map-iso-Ab f y)
  preserves-add-iso-Ab =
    preserves-mul-iso-Group (group-Ab A) (group-Ab B)

  is-iso-iso-Ab : (f : iso-Ab) → is-iso-Ab A B (hom-iso-Ab f)
  is-iso-iso-Ab = is-iso-iso-Group (group-Ab A) (group-Ab B)

  hom-inv-iso-Ab : iso-Ab → hom-Ab B A
  hom-inv-iso-Ab = hom-inv-iso-Group (group-Ab A) (group-Ab B)

  map-inv-iso-Ab : iso-Ab → type-Ab B → type-Ab A
  map-inv-iso-Ab = map-inv-iso-Group (group-Ab A) (group-Ab B)

  preserves-add-inv-iso-Ab :
    (f : iso-Ab) {x y : type-Ab B} →
    map-inv-iso-Ab f (add-Ab B x y) ＝
    add-Ab A (map-inv-iso-Ab f x) (map-inv-iso-Ab f y)
  preserves-add-inv-iso-Ab =
    preserves-mul-inv-iso-Group (group-Ab A) (group-Ab B)

  is-section-hom-inv-iso-Ab :
    (f : iso-Ab) →
    comp-hom-Ab B A B (hom-iso-Ab f) (hom-inv-iso-Ab f) ＝ id-hom-Ab B
  is-section-hom-inv-iso-Ab =
    is-section-hom-inv-iso-Group (group-Ab A) (group-Ab B)

  is-section-map-inv-iso-Ab :
    (f : iso-Ab) → (map-iso-Ab f ∘ map-inv-iso-Ab f) ~ id
  is-section-map-inv-iso-Ab =
    is-section-map-inv-iso-Group (group-Ab A) (group-Ab B)

  is-retraction-hom-inv-iso-Ab :
    (f : iso-Ab) →
    comp-hom-Ab A B A (hom-inv-iso-Ab f) (hom-iso-Ab f) ＝ id-hom-Ab A
  is-retraction-hom-inv-iso-Ab =
    is-retraction-hom-inv-iso-Group (group-Ab A) (group-Ab B)

  is-retraction-map-inv-iso-Ab :
    (f : iso-Ab) → (map-inv-iso-Ab f ∘ map-iso-Ab f) ~ id
  is-retraction-map-inv-iso-Ab =
    is-retraction-map-inv-iso-Group (group-Ab A) (group-Ab B)
```

### The identity isomorphism of abelian groups

```agda
id-iso-Ab : {l : Level} (A : Ab l) → iso-Ab A A
id-iso-Ab A = id-iso-Group (group-Ab A)
```

## Properties

### Isomorphisms characterize identifications of abelian groups

```agda
iso-eq-Ab :
  {l : Level} (A B : Ab l) → A ＝ B → iso-Ab A B
iso-eq-Ab A B p = iso-eq-Group (group-Ab A) (group-Ab B) (ap pr1 p)

abstract
  equiv-iso-eq-Ab' :
    {l : Level} (A B : Ab l) → (A ＝ B) ≃ iso-Ab A B
  equiv-iso-eq-Ab' A B =
    ( extensionality-Group' (group-Ab A) (group-Ab B)) ∘e
    ( equiv-ap-inclusion-subtype is-abelian-prop-Group {A} {B})

abstract
  is-torsorial-iso-Ab :
    {l : Level} (A : Ab l) → is-torsorial (λ (B : Ab l) → iso-Ab A B)
  is-torsorial-iso-Ab {l} A =
    is-contr-equiv'
      ( Σ (Ab l) (Id A))
      ( equiv-tot (equiv-iso-eq-Ab' A))
      ( is-torsorial-Id A)

is-equiv-iso-eq-Ab :
  {l : Level} (A B : Ab l) → is-equiv (iso-eq-Ab A B)
is-equiv-iso-eq-Ab A =
  fundamental-theorem-id
    ( is-torsorial-iso-Ab A)
    ( iso-eq-Ab A)

eq-iso-Ab :
  {l : Level} (A B : Ab l) → iso-Ab A B → A ＝ B
eq-iso-Ab A B = map-inv-is-equiv (is-equiv-iso-eq-Ab A B)
```

### A homomorphism of abelian groups is an isomorphism if and only if its underlying map is an equivalence

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  is-iso-is-equiv-hom-Ab :
    (f : hom-Ab A B) → is-equiv-hom-Ab A B f → is-iso-Ab A B f
  is-iso-is-equiv-hom-Ab = is-iso-is-equiv-hom-Group (group-Ab A) (group-Ab B)

  is-equiv-is-iso-Ab :
    (f : hom-Ab A B) → is-iso-Ab A B f → is-equiv-hom-Ab A B f
  is-equiv-is-iso-Ab = is-equiv-is-iso-Group (group-Ab A) (group-Ab B)

  equiv-iso-equiv-Ab : equiv-Ab A B ≃ iso-Ab A B
  equiv-iso-equiv-Ab = equiv-iso-equiv-Group (group-Ab A) (group-Ab B)

  iso-equiv-Ab : equiv-Ab A B → iso-Ab A B
  iso-equiv-Ab = iso-equiv-Group (group-Ab A) (group-Ab B)
```
