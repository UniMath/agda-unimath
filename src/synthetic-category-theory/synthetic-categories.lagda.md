# Synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.synthetic-categories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.globular-types
```

</details>

## Idea

{{#concept "synthetic categories"}} are defined by establishing the rules on the type of all synthetic categories. In particular, synthetic categories are not defined to be types of objects equipped with hom-sets and so on, but they are simply elements of the type of synthetic categories, which is given sufficient structure so that we can work with its elements as if they are categories.

The primitive notions of synthetic categories are:
1. Synthetic categories
2. Functors between them,
3. Natural isomorphisms between them,
4. Natural isomorphisms between those,
5. and so on.

The type of synthetic categories is furthermore postulated to have the following structure:
1. A terminal category
2. An initial category
3. Cartesian product categories
4. Coproduct categories
5. Pullbacks of categories
6. Functor categories
7. A representing arrow
8. A representing commuting triangle

Furthermore, coproducts are assumed to be universal, there is a Segal axiom and a Rezk axiom, and some that we haven't listed here.

The theory of synthetic categories is not intended to be infinitely coherent. Similar to [wild category theory](wild-category-theory.md), some higher coherences are obviously missing. Nevertheless, the theory is strong enough to embody a large amount of higher category theory.

## Definitions

### The type of synthetic categories

```agda
module _
  {l : Level}
  where

  language-Synthetic-Category-Theory : UU (lsuc l)
  language-Synthetic-Category-Theory = Globular-Type l l

  category-Synthetic-Category-Theory :
    language-Synthetic-Category-Theory → UU l
  category-Synthetic-Category-Theory = 0-cell-Globular-Type

  functor-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory) →
    (C D : category-Synthetic-Category-Theory κ) → UU l
  functor-Synthetic-Category-Theory = 1-cell-Globular-Type

  isomorphism-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory)
    {C D : category-Synthetic-Category-Theory κ}
    (F G : functor-Synthetic-Category-Theory κ C D) → UU l
  isomorphism-Synthetic-Category-Theory = 2-cell-Globular-Type

  record
    identity-Synthetic-Category-Theory
      (κ : language-Synthetic-Category-Theory) : UU l
    where
    coinductive
    field
      id-functor-Synthetic-Category-Theory :
        (C : category-Synthetic-Category-Theory κ) →
        functor-Synthetic-Category-Theory κ C C
      id-iso-Synthetic-Category-Theory :
        {C D : category-Synthetic-Category-Theory κ} →
        identity-Synthetic-Category-Theory
          ( globular-type-1-cell-Globular-Type κ C D)

  record
    composition-Synthetic-Category-Theory
      (κ : language-Synthetic-Category-Theory) : UU l
    where
    coinductive
    field
      comp-functor-Synthetic-Category-Theory :
        {C D E : category-Synthetic-Category-Theory κ} →
        functor-Synthetic-Category-Theory κ D E →
        functor-Synthetic-Category-Theory κ C D →
        functor-Synthetic-Category-Theory κ C E
      comp-iso-Synthetic-Category-Theory :
        {C D : category-Synthetic-Category-Theory κ} →
        composition-Synthetic-Category-Theory
          ( globular-type-1-cell-Globular-Type κ C D)
```
