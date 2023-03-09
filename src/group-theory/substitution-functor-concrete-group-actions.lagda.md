# The substitution functor of concrete group actions

```agda
module group-theory.substitution-functor-concrete-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
open import group-theory.homomorphisms-concrete-groups
```

</details>

## Definition

### Substitution of concrete group actions

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2)
  (f : hom-Concrete-Group G H)
  where

  subst-action-Concrete-Group :
    {l : Level} →
    action-Concrete-Group l H → action-Concrete-Group l G
  subst-action-Concrete-Group Y x =
    Y (classifying-map-hom-Concrete-Group G H f x)
```
