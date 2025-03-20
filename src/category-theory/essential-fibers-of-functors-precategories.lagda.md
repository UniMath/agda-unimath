# Essential fibers of functors between precategories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.essential-fibers-of-functors-precategories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories funext
open import category-theory.isomorphisms-in-precategories funext
open import category-theory.precategories funext

open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

Given a [functor](category-theory.functors-precategories.md) `F : C → D` between
[precategories](category-theory.precategories.md) and an object `y : D` we can
form the **essential fiber** of `y` over `F` as the
[subprecategory](category-theory.subprecategories.md) of `C` spanned by... TODO

## Definitions

### The essential fiber over an object

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  essential-fiber-functor-Precategory : (y : obj-Precategory D) → UU (l1 ⊔ l4)
  essential-fiber-functor-Precategory y =
    Σ ( obj-Precategory C)
      ( λ x → iso-Precategory D (obj-functor-Precategory C D F x) y)

  essential-fiber-functor-Precategory' : (y : obj-Precategory D) → UU (l1 ⊔ l4)
  essential-fiber-functor-Precategory' y =
    Σ ( obj-Precategory C)
      ( λ x → iso-Precategory D y (obj-functor-Precategory C D F x))
```

## See also

- [Essentially surjective functors between precategories](category-theory.essentially-surjective-functors-precategories.md)
- [Split essentially surjective functors between precategories](category-theory.split-essentially-surjective-functors-precategories.md)

## External links

- [Essential Fibres](https://1lab.dev/Cat.Functor.Properties.html#essential-fibres)
  at 1lab
- [essential fiber](https://ncatlab.org/nlab/show/essential+fiber) at $n$Lab
