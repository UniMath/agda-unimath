# The Yoneda lemma for categories

```agda
module category-theory.yoneda-lemma-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.copresheaf-categories
open import category-theory.natural-transformations-functors-from-small-to-large-categories
open import category-theory.representable-functors-categories
open import category-theory.yoneda-lemma-precategories

open import foundation.category-of-sets
open import foundation.equivalences
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "Yoneda lemma" Disambiguation="for set-level categories" WD="Yoneda lemma" WDID=Q320577 Agda=lemma-yoneda-Category}}
states that, given a [category](category-theory.categories.md) `C`, an object
`c`, and a [functor](category-theory.functors-categories.md) `F` from `C` to the
[category of sets](foundation.category-of-sets.md)

```text
  F : C → Set,
```

there is an [equivalence](foundation-core.equivalences.md) between the
[set of natural transformations](category-theory.natural-transformations-functors-categories.md)
from the functor
[represented](category-theory.representable-functors-categories.md) by `c` to
`F` and the [set](foundation-core.sets.md) `F c`.

```text
  Nat(Hom(c , -) , F) ≃ F c
```

More precisely, the Yoneda lemma asserts that the map from the type of natural
transformations to the type `F c` defined by evaluating the component of the
natural transformation at the object `c` at the identity arrow on `c` is an
equivalence.

## Theorem

### The Yoneda lemma into the large category of sets

```agda
module _
  {l1 l2 l3 : Level} (C : Category l1 l2) (c : obj-Category C)
  (F : copresheaf-Precategory (precategory-Category C) l3)
  where

  map-yoneda-Category :
    hom-copresheaf-Precategory
      ( precategory-Category C) (representable-functor-Category C c) F →
    element-copresheaf-Precategory (precategory-Category C) F c
  map-yoneda-Category =
    map-yoneda-Precategory (precategory-Category C) c F
```

The inverse to the Yoneda map:

```agda
  hom-family-extension-yoneda-Category :
    (u : element-copresheaf-Precategory (precategory-Category C) F c) →
    hom-family-functor-Small-Large-Category
      C Set-Large-Category (representable-functor-Category C c) F
  hom-family-extension-yoneda-Category =
    hom-family-extension-yoneda-Precategory (precategory-Category C) c F

  naturality-extension-yoneda-Category :
    (u : element-copresheaf-Precategory (precategory-Category C) F c) →
    is-natural-transformation-Small-Large-Category
      C Set-Large-Category (representable-functor-Category C c) F
      ( hom-family-extension-yoneda-Category u)
  naturality-extension-yoneda-Category =
    naturality-extension-yoneda-Precategory (precategory-Category C) c F

  extension-yoneda-Category :
    element-copresheaf-Precategory (precategory-Category C) F c →
    hom-copresheaf-Precategory
      ( precategory-Category C) (representable-functor-Category C c) F
  extension-yoneda-Category =
    extension-yoneda-Precategory (precategory-Category C) c F

  lemma-yoneda-Category : is-equiv map-yoneda-Category
  lemma-yoneda-Category = lemma-yoneda-Precategory (precategory-Category C) c F

  equiv-lemma-yoneda-Category :
    hom-copresheaf-Precategory
      ( precategory-Category C) (representable-functor-Category C c) F ≃
    element-copresheaf-Precategory (precategory-Category C) F c
  equiv-lemma-yoneda-Category =
    equiv-lemma-yoneda-Precategory (precategory-Category C) c F
```

## Corollaries

### The Yoneda lemma for representable functors

An important special-case of the Yoneda lemma is when `F` is itself a
representable functor `F = Hom(-, d)`.

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2) (c d : obj-Category C)
  where

  equiv-lemma-yoneda-representable-Category :
    hom-copresheaf-Precategory
      ( precategory-Category C)
      ( representable-functor-Category C c)
      ( representable-functor-Category C d) ≃
    hom-Category C d c
  equiv-lemma-yoneda-representable-Category =
    equiv-lemma-yoneda-Category C c (representable-functor-Category C d)
```

## See also

- [Presheaf categories](category-theory.presheaf-categories.md)

## External links

- [The Yoneda embedding](https://1lab.dev/Cat.Functor.Hom.html#the-yoneda-embedding)
  at 1lab
- [Yoneda lemma](https://ncatlab.org/nlab/show/Yoneda+lemma) at $n$Lab
- [The Yoneda lemma](https://www.math3ma.com/blog/the-yoneda-lemma) at Math3ma
- [Yoneda lemma](https://en.wikipedia.org/wiki/Yoneda_lemma) at Wikipedia
- [Yoneda lemma](https://www.wikidata.org/wiki/Q320577) at Wikidata
