# The universal property of lists with respect to wild monoids

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module wild-algebra.universal-property-lists-wild-monoids where
```

## Idea

The type of lists of elements of `A` is the initial wild monoid equipped with a map from `A` into it.

```agda
list-Wild-Unital-Magma :
  {l : Level} (X : UU l) → Wild-Unital-Magma l
list-Wild-Unital-Magma X =
  pair
    ( pair (list X) nil)
    ( pair
      ( concat-list)
      ( pair
        ( left-unit-law-concat-list)
        ( pair right-unit-law-concat-list refl)))
```
