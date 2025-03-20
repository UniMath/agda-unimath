# Essentially surjective functors between precategories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.essentially-surjective-functors-precategories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories funext
open import category-theory.isomorphisms-in-precategories funext
open import category-theory.precategories funext

open import foundation.dependent-pair-types
open import foundation.existential-quantification funext
open import foundation.propositions funext
open import foundation.universe-levels
```

</details>

## Idea

A [functor](category-theory.functors-precategories.md) `F : C → D` between
[precategories](category-theory.precategories.md) is
{{#concept "essentially surjective" Disambiguation="functor between set-level precategories" WDID=Q140283 WD="essentially surjective functor" Agda=is-essentially-surjective-functor-Precategory Agda=essentially-surjective-functor-Precategory}}
if there for every object `y : D`
[merely exists](foundation.existential-quantification.md) an object `x : C` such
that `F x ≅ y`.

## Definitions

### The predicate of being essentially surjective

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-essentially-surjective-prop-functor-Precategory : Prop (l1 ⊔ l3 ⊔ l4)
  is-essentially-surjective-prop-functor-Precategory =
    Π-Prop
      ( obj-Precategory D)
      ( λ y →
        exists-structure-Prop
          ( obj-Precategory C)
          ( λ x → iso-Precategory D (obj-functor-Precategory C D F x) y))

  is-essentially-surjective-functor-Precategory : UU (l1 ⊔ l3 ⊔ l4)
  is-essentially-surjective-functor-Precategory =
    ( y : obj-Precategory D) →
    exists-structure
      ( obj-Precategory C)
      ( λ x → iso-Precategory D (obj-functor-Precategory C D F x) y)

  is-prop-is-essentially-surjective-functor-Precategory :
    is-prop is-essentially-surjective-functor-Precategory
  is-prop-is-essentially-surjective-functor-Precategory =
    is-prop-type-Prop is-essentially-surjective-prop-functor-Precategory
```

### The type of essentially surjective functors

```agda
essentially-surjective-functor-Precategory :
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
essentially-surjective-functor-Precategory C D =
  Σ ( functor-Precategory C D)
    ( is-essentially-surjective-functor-Precategory C D)

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : essentially-surjective-functor-Precategory C D)
  where

  functor-essentially-surjective-functor-Precategory :
    functor-Precategory C D
  functor-essentially-surjective-functor-Precategory = pr1 F

  is-essentially-surjective-essentially-surjective-functor-Precategory :
    is-essentially-surjective-functor-Precategory C D
      ( functor-essentially-surjective-functor-Precategory)
  is-essentially-surjective-essentially-surjective-functor-Precategory = pr2 F

  obj-essentially-surjective-functor-Precategory :
    obj-Precategory C → obj-Precategory D
  obj-essentially-surjective-functor-Precategory =
    obj-functor-Precategory C D
      ( functor-essentially-surjective-functor-Precategory)

  hom-essentially-surjective-functor-Precategory :
    {x y : obj-Precategory C} →
    hom-Precategory C x y →
    hom-Precategory D
      ( obj-essentially-surjective-functor-Precategory x)
      ( obj-essentially-surjective-functor-Precategory y)
  hom-essentially-surjective-functor-Precategory =
    hom-functor-Precategory C D
      ( functor-essentially-surjective-functor-Precategory)
```

## Properties

### Precomposing by essentially surjective functors define fully faithful functors

This remains to be shown. This is Lemma 8.2 of _Univalent Categories and the
Rezk completion_.

## See also

- [Split essentially surjective functor between precategories](category-theory.split-essentially-surjective-functors-precategories.md)

## References

{{#bibliography}} {{#reference AKS15}}

## External links

- [Essential Fibres](https://1lab.dev/Cat.Functor.Properties.html#essential-fibres)
  at 1lab
- [essentially surjective functor](https://ncatlab.org/nlab/show/essentially+surjective+functor)
  at $n$Lab
- [Fully Faithful and Essentially Surjective Functors](https://kerodon.net/tag/01JG)
  at Kerodon
- [Essentially surjective functor](https://en.wikipedia.org/wiki/Essentially_surjective_functor)
  at Wikipedia
- [essentially surjective functor](https://www.wikidata.org/wiki/Q140283) at
  wikidata
