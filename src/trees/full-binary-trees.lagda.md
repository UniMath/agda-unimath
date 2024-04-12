# Full binary trees

```agda
module trees.full-binary-trees where
```

<details><sumary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.empty-types
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A {{#concept "plane tree" Agda=full-binary-tree}} is a finite tree that can be
drawn on a plane with the root at the bottom, and all branches directed upwards.
More preciesly, a plane tree consists of a root and a family of plane trees
indexed by a
[standard finite type](univalent-combinatorics.standard-finite-types.md).

## Definitions

### Plane trees

```agda
data full-binary-tree : UU lzero where
  leaf-full-binary-tree : full-binary-tree
  join-full-binary-tree : (s t : full-binary-tree) → full-binary-tree
```
