# Natural numbers object in a precategory

```agda
module category-theory.natural-numbers-object-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories
open import category-theory.terminal-objects-precategories

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unique-existence
open import foundation.universe-levels
```

</details>

## Idea

Let `C` be a precategory with a terminal object `t`. A natural numbers object in `C` is an object `n` with morphisms `z : hom t n` and `s : hom n n` such that for any object `x` and morphisms `q : hom t x` and `f : hom x x` there exists a unique `u : hom n x` such that:
- u ∘ z = q
- u ∘ s = f ∘ u.

```agda
module _ {l1 l2} (C : Precat l1 l2) ((t , _) : terminal-object C) where

  is-natural-numbers-object : (n : obj-Precat C)
                            → type-hom-Precat C t n
                            → type-hom-Precat C n n
                            → UU (l1 ⊔ l2)
  is-natural-numbers-object n z s =
    (x : obj-Precat C)
    (q : type-hom-Precat C t x)
    (f : type-hom-Precat C x x) →
    ∃! (type-hom-Precat C n x) λ u →
       (comp-hom-Precat C u z ＝ q)
     × (comp-hom-Precat C u s ＝ comp-hom-Precat C f u)

  natural-numbers-object : UU (l1 ⊔ l2)
  natural-numbers-object =
    Σ (obj-Precat C) λ n →
    Σ (type-hom-Precat C t n) λ z →
    Σ (type-hom-Precat C n n) λ s →
      is-natural-numbers-object n z s

module _ {l1 l2} (C : Precat l1 l2) ((t , p) : terminal-object C)
  (nno : natural-numbers-object C (t , p)) where

  object-natural-numbers-object : obj-Precat C
  object-natural-numbers-object = pr1 nno

  zero-natural-numbers-object : type-hom-Precat C t object-natural-numbers-object
  zero-natural-numbers-object = pr1 (pr2 nno)

  succ-natural-numbers-object : type-hom-Precat C object-natural-numbers-object object-natural-numbers-object
  succ-natural-numbers-object = pr1 (pr2 (pr2 nno))

  module _ (x : obj-Precat C) (q : type-hom-Precat C t x)
    (f : type-hom-Precat C x x) where

    morphism-natural-numbers-object : type-hom-Precat C object-natural-numbers-object x
    morphism-natural-numbers-object = pr1 (pr1 (pr2 (pr2 (pr2 nno)) x q f))

    morphism-natural-numbers-object-zero-comm :
      comp-hom-Precat C morphism-natural-numbers-object zero-natural-numbers-object ＝ q
    morphism-natural-numbers-object-zero-comm = pr1 (pr2 (pr1 (pr2 (pr2 (pr2 nno)) x q f)))

    morphism-natural-numbers-object-succ-comm :
      comp-hom-Precat C morphism-natural-numbers-object succ-natural-numbers-object ＝
      comp-hom-Precat C f morphism-natural-numbers-object
    morphism-natural-numbers-object-succ-comm = pr2 (pr2 (pr1 (pr2 (pr2 (pr2 nno)) x q f)))

    is-unique-morphism-natural-numbers-object :
      (u' : type-hom-Precat C object-natural-numbers-object x) →
      comp-hom-Precat C u' zero-natural-numbers-object ＝ q →
      comp-hom-Precat C u' succ-natural-numbers-object ＝ comp-hom-Precat C f u' →
      morphism-natural-numbers-object ＝ u'
    is-unique-morphism-natural-numbers-object u' α β =
      ap pr1 (pr2 (pr2 (pr2 (pr2 nno)) x q f) (u' , α , β))
```
