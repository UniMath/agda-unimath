# Embeddings of groups

```agda
module group-theory.embeddings-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.subgroups
```

</details>

## Idea

Embeddings of groups are group homomorphisms of which the underlying map is an
embedding

## Definitions

### Embeddings of groups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  is-emb-hom-Group : (hom-Group G H) → UU (l1 ⊔ l2)
  is-emb-hom-Group h = is-emb (map-hom-Group G H h)

  emb-Group : UU (l1 ⊔ l2)
  emb-Group = Σ (hom-Group G H) is-emb-hom-Group

  hom-emb-Group : emb-Group → hom-Group G H
  hom-emb-Group = pr1

  map-emb-hom-Group : emb-Group → type-Group G → type-Group H
  map-emb-hom-Group f = map-hom-Group G H (hom-emb-Group f)

  is-emb-map-emb-hom-Group : (f : emb-Group) → is-emb (map-emb-hom-Group f)
  is-emb-map-emb-hom-Group = pr2
```

### The type of all embeddings into a group

```agda
emb-Group-Slice :
  (l : Level) {l1 : Level} (G : Group l1) → UU ((lsuc l) ⊔ l1)
emb-Group-Slice l G = Σ ( Group l) (λ H → emb-Group H G)

emb-group-slice-Subgroup :
  { l1 l2 : Level} (G : Group l1) →
  Subgroup l2 G → emb-Group-Slice (l1 ⊔ l2) G
pr1 (emb-group-slice-Subgroup G P) = group-Subgroup G P
pr1 (pr2 (emb-group-slice-Subgroup G P)) = hom-inclusion-Subgroup G P
pr2 (pr2 (emb-group-slice-Subgroup G P)) =
  is-emb-inclusion-Subgroup G P
```
