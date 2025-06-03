# Universe levels

```agda
module foundation.universe-levels where

open import Agda.Primitive
  using (Level ; lzero ; lsuc ; _⊔_)
  renaming (Set to UU ; Setω to UUω)
  public
```

## Idea

We import Agda's built in mechanism of universe levels. The universes are called
`UU`, which stands for _univalent universe_, although we will not immediately
assume that universes are univalent. This is done in
[`foundation.univalence`](foundation.univalence.md).
