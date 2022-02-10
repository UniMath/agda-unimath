# Counting the elements in the fiber of a map

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.counting-fibers-of-maps where
```

### If A and B can be counted, then the fibers of a map f : A → B can be counted

```agda
count-fib :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  count A → count B → (y : B) → count (fib f y)
count-fib f count-A count-B =
  count-fiber-count-Σ count-B (count-equiv' (equiv-total-fib f) count-A)
```
