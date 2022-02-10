# Counting the elements of coproduct types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.counting-coproduct-types where
```

### Types equipped with a count are closed under coproducts

```agda
count-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  count X → count Y → count (coprod X Y)
pr1 (count-coprod (pair k e) (pair l f)) = add-ℕ k l
pr2 (count-coprod (pair k e) (pair l f)) =
  (equiv-coprod e f) ∘e (inv-equiv (coprod-Fin k l))

abstract
  number-of-elements-count-coprod :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : count X) (f : count Y) →
    Id ( number-of-elements-count (count-coprod e f))
      ( add-ℕ (number-of-elements-count e) (number-of-elements-count f))
  number-of-elements-count-coprod (pair k e) (pair l f) = refl
```

## A coproduct X + Y has a count if and only if both X and Y have a count.

```agda
is-left : {l1 l2 : Level} {X : UU l1} {Y : UU l2} → coprod X Y → UU lzero
is-left (inl x) = unit
is-left (inr x) = empty

equiv-left-summand :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (Σ (coprod X Y) is-left) ≃ X
equiv-left-summand {l1} {l2} {X} {Y} =
  ( ( right-unit-law-coprod X) ∘e
    ( equiv-coprod right-unit-law-prod right-absorption-prod)) ∘e
  ( right-distributive-Σ-coprod X Y is-left)

count-is-left :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (t : coprod X Y) → count (is-left t)
count-is-left (inl x) = count-unit
count-is-left (inr x) = count-empty

count-left-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (coprod X Y) → count X
count-left-coprod e = count-equiv equiv-left-summand (count-Σ e count-is-left)

is-right : {l1 l2 : Level} {X : UU l1} {Y : UU l2} → coprod X Y → UU lzero
is-right (inl x) = empty
is-right (inr x) = unit

equiv-right-summand :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (Σ (coprod X Y) is-right) ≃ Y
equiv-right-summand {l1} {l2} {X} {Y} =
  ( ( left-unit-law-coprod Y) ∘e
    ( equiv-coprod right-absorption-prod right-unit-law-prod)) ∘e
    ( right-distributive-Σ-coprod X Y is-right)

count-is-right :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (t : coprod X Y) → count (is-right t)
count-is-right (inl x) = count-empty
count-is-right (inr x) = count-unit

count-right-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (coprod X Y) → count Y
count-right-coprod e =
  count-equiv equiv-right-summand (count-Σ e count-is-right)
```
