# Embeddings of abelian groups

```agda
module group-theory.embeddings-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.embeddings
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.embeddings-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.subgroups-abelian-groups
```

</details>

## Idea

Embeddings of groups are group homomorphisms of which the underlying map is an
embedding

## Definitions

### Embeddings of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  is-emb-hom-Ab : (hom-Ab A B) → UU (l1 ⊔ l2)
  is-emb-hom-Ab = is-emb-hom-Group (group-Ab A) (group-Ab B)

  emb-Ab : UU (l1 ⊔ l2)
  emb-Ab = emb-Group (group-Ab A) (group-Ab B)

  hom-emb-Ab : emb-Ab → hom-Ab A B
  hom-emb-Ab = hom-emb-Group (group-Ab A) (group-Ab B)

  map-emb-hom-Ab : emb-Ab → type-Ab A → type-Ab B
  map-emb-hom-Ab = map-emb-hom-Group (group-Ab A) (group-Ab B)

  is-emb-map-emb-hom-Ab : (f : emb-Ab) → is-emb (map-emb-hom-Ab f)
  is-emb-map-emb-hom-Ab =
    is-emb-map-emb-hom-Group (group-Ab A) (group-Ab B)
```

### The type of all embeddings into an abelian group

```agda
emb-Ab-Slice :
  (l : Level) {l1 : Level} (A : Ab l1) → UU ((lsuc l) ⊔ l1)
emb-Ab-Slice l A = emb-Group-Slice l (group-Ab A)

emb-ab-slice-Subgroup-Ab :
  { l1 l2 : Level} (A : Ab l1) →
  Subgroup-Ab l2 A → emb-Ab-Slice (l1 ⊔ l2) A
emb-ab-slice-Subgroup-Ab A = emb-group-slice-Subgroup (group-Ab A)
```
