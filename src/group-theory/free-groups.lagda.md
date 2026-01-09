# Free groups

```agda
module group-theory.free-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.universe-levels
```

</details>

## Idea

## Definition

```agda
data word-free-Group {l : Level} (A : UU l) : UU l where
  in-generator-word-free-Group : A → word-free-Group A
  inv-word-free-Group : word-free-Group A → word-free-Group A
  mul-word-free-Group :
    word-free-Group A → word-free-Group A → word-free-Group A

data equiv-word-free-Group {l : Level} (A : UU l) : Relation l (word-free-Group A) where
```
