# Synthetic category theory

```agda
{-# OPTIONS --guardedness #-}
```

## Idea

Synthetic category theory is an approach to the foundation of mathematics in
which the principal objects are ∞-categories. The theory is due to Cisinski et
al. {{#cite Cisinski24}}, which we will follow here closely. Synthetic category
theory differs from [wild category theory](wild-category-theory.md) in the sense
that wild categories are defined as structured objects, i.e., their definition
follows an "analytic" approach, whereas synthetic categories are defined by the
rules for the type of all synthetic categories.

Some core principles of higher category theory include:

- To express that two things are equal we specify an isomorphism between them.
- Any valid statement or construction in category theory must respect
  isomorphisms {{#cite Makkai98}}.

## Files in the Synthetic category theory folder

```agda
module synthetic-category-theory where

open import synthetic-category-theory.equivalence-of-synthetic-categories public
open import synthetic-category-theory.synthetic-categories public
```

## References

{{#bibliography}}
