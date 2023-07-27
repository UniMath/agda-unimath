# Isomorphisms of abelian groups

```agda
module group-theory.isomorphisms-abelian-groups where
```

<details><summary>Imports</summary>

```agda
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
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.isomorphisms-groups
open import group-theory.isomorphisms-semigroups
```

</details>

## Idea

Isomorphisms between abelian groups are just isomorphisms between their
underlying groups.

## Definition

```agda
is-iso-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  ( f : type-hom-Ab A B) → UU (l1 ⊔ l2)
is-iso-hom-Ab A B =
  is-iso-hom-Semigroup (semigroup-Ab A) (semigroup-Ab B)

inv-is-iso-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : type-hom-Ab A B) →
  is-iso-hom-Ab A B f → type-hom-Ab B A
inv-is-iso-hom-Ab A B f = pr1

map-inv-is-iso-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : type-hom-Ab A B) →
  is-iso-hom-Ab A B f → type-Ab B → type-Ab A
map-inv-is-iso-hom-Ab A B f is-iso-f =
  map-hom-Ab B A (inv-is-iso-hom-Ab A B f is-iso-f)

is-section-inv-is-iso-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : type-hom-Ab A B) →
  ( is-iso-f : is-iso-hom-Ab A B f) →
  Id (comp-hom-Ab B A B f (inv-is-iso-hom-Ab A B f is-iso-f)) (id-hom-Ab B)
is-section-inv-is-iso-hom-Ab A B f is-iso-f = pr1 (pr2 is-iso-f)

is-section-map-inv-is-iso-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : type-hom-Ab A B) →
  ( is-iso-f : is-iso-hom-Ab A B f) →
  ( (map-hom-Ab A B f) ∘ (map-hom-Ab B A (inv-is-iso-hom-Ab A B f is-iso-f))) ~
  id
is-section-map-inv-is-iso-hom-Ab A B f is-iso-f =
  htpy-eq-hom-Ab B B
    ( comp-hom-Ab B A B f (inv-is-iso-hom-Ab A B f is-iso-f))
    ( id-hom-Ab B)
    ( is-section-inv-is-iso-hom-Ab A B f is-iso-f)

is-retraction-inv-is-iso-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : type-hom-Ab A B) →
  ( is-iso-f : is-iso-hom-Ab A B f) →
  Id (comp-hom-Ab A B A (inv-is-iso-hom-Ab A B f is-iso-f) f) (id-hom-Ab A)
is-retraction-inv-is-iso-hom-Ab A B f is-iso-f = pr2 (pr2 is-iso-f)

is-retraction-map-inv-is-iso-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : type-hom-Ab A B) →
  ( is-iso-f : is-iso-hom-Ab A B f) →
  ( (map-inv-is-iso-hom-Ab A B f is-iso-f) ∘ (map-hom-Ab A B f)) ~ id
is-retraction-map-inv-is-iso-hom-Ab A B f is-iso-f =
  htpy-eq-hom-Ab A A
    ( comp-hom-Ab A B A (inv-is-iso-hom-Ab A B f is-iso-f) f)
    ( id-hom-Ab A)
    ( is-retraction-inv-is-iso-hom-Ab A B f is-iso-f)

is-prop-is-iso-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : type-hom-Ab A B) →
  is-prop (is-iso-hom-Ab A B f)
is-prop-is-iso-hom-Ab A B f =
  is-prop-is-iso-hom-Semigroup (semigroup-Ab A) (semigroup-Ab B) f

iso-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) → UU (l1 ⊔ l2)
iso-Ab A B = Σ (type-hom-Ab A B) (is-iso-hom-Ab A B)

hom-iso-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  iso-Ab A B → type-hom-Ab A B
hom-iso-Ab A B = pr1

is-iso-hom-iso-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  ( f : iso-Ab A B) → is-iso-hom-Ab A B (hom-iso-Ab A B f)
is-iso-hom-iso-Ab A B = pr2

inv-hom-iso-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  iso-Ab A B → type-hom-Ab B A
inv-hom-iso-Ab A B f =
  inv-is-iso-hom-Ab A B
    ( hom-iso-Ab A B f)
    ( is-iso-hom-iso-Ab A B f)

id-iso-Ab :
  {l1 : Level} (A : Ab l1) → iso-Ab A A
id-iso-Ab A = id-iso-Group (group-Ab A)

iso-eq-Ab :
  { l1 : Level} (A B : Ab l1) → Id A B → iso-Ab A B
iso-eq-Ab A .A refl = id-iso-Ab A

abstract
  equiv-iso-eq-Ab' :
    {l1 : Level} (A B : Ab l1) → Id A B ≃ iso-Ab A B
  equiv-iso-eq-Ab' A B =
    ( extensionality-Group' (group-Ab A) (group-Ab B)) ∘e
    ( equiv-ap-inclusion-subtype is-abelian-group-Prop {A} {B})

abstract
  is-contr-total-iso-Ab :
    { l1 : Level} (A : Ab l1) → is-contr (Σ (Ab l1) (iso-Ab A))
  is-contr-total-iso-Ab {l1} A =
    is-contr-equiv'
      ( Σ (Ab l1) (Id A))
      ( equiv-tot (equiv-iso-eq-Ab' A))
      ( is-contr-total-path A)

is-equiv-iso-eq-Ab :
  { l1 : Level} (A B : Ab l1) → is-equiv (iso-eq-Ab A B)
is-equiv-iso-eq-Ab A =
  fundamental-theorem-id
    ( is-contr-total-iso-Ab A)
    ( iso-eq-Ab A)

eq-iso-Ab :
  { l1 : Level} (A B : Ab l1) → iso-Ab A B → Id A B
eq-iso-Ab A B = map-inv-is-equiv (is-equiv-iso-eq-Ab A B)
```
