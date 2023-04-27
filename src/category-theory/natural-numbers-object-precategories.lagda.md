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

Let `C` be a precategory with a terminal object `t`. A natural numbers object in
`C` is an object `n` with morphisms `z : hom t n` and `s : hom n n` such that
for any object `x` and morphisms `q : hom t x` and `f : hom x x` there exists a
unique `u : hom n x` such that:

- u ∘ z = q
- u ∘ s = f ∘ u.

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2) ((t , _) : terminal-object-Precat C)
  where

  is-natural-numbers-object-Precat : (n : obj-Precat C)
                            → type-hom-Precat C t n
                            → type-hom-Precat C n n
                            → UU (l1 ⊔ l2)
  is-natural-numbers-object-Precat n z s =
    (x : obj-Precat C)
    (q : type-hom-Precat C t x)
    (f : type-hom-Precat C x x) →
    ∃! (type-hom-Precat C n x) λ u →
       (comp-hom-Precat C u z ＝ q)
     × (comp-hom-Precat C u s ＝ comp-hom-Precat C f u)

  natural-numbers-object-Precat : UU (l1 ⊔ l2)
  natural-numbers-object-Precat =
    Σ (obj-Precat C) λ n →
    Σ (type-hom-Precat C t n) λ z →
    Σ (type-hom-Precat C n n) λ s →
      is-natural-numbers-object-Precat n z s

module _
  {l1 l2 : Level} (C : Precat l1 l2) ((t , p) : terminal-object-Precat C)
  (nno : natural-numbers-object-Precat C (t , p))
  where

  object-natural-numbers-object-Precat : obj-Precat C
  object-natural-numbers-object-Precat = pr1 nno

  zero-natural-numbers-object-Precat :
    type-hom-Precat C t object-natural-numbers-object-Precat
  zero-natural-numbers-object-Precat = pr1 (pr2 nno)

  succ-natural-numbers-object-Precat :
    type-hom-Precat C
      ( object-natural-numbers-object-Precat)
      ( object-natural-numbers-object-Precat)
  succ-natural-numbers-object-Precat = pr1 (pr2 (pr2 nno))

  module _
    (x : obj-Precat C)
    (q : type-hom-Precat C t x)
    (f : type-hom-Precat C x x)
    where

    morphism-natural-numbers-object-Precat :
      type-hom-Precat C object-natural-numbers-object-Precat x
    morphism-natural-numbers-object-Precat =
      pr1 (pr1 (pr2 (pr2 (pr2 nno)) x q f))

    morphism-natural-numbers-object-Precat-zero-comm :
      comp-hom-Precat C morphism-natural-numbers-object-Precat
        ( zero-natural-numbers-object-Precat) ＝ q
    morphism-natural-numbers-object-Precat-zero-comm =
      pr1 (pr2 (pr1 (pr2 (pr2 (pr2 nno)) x q f)))

    morphism-natural-numbers-object-Precat-succ-comm :
      comp-hom-Precat
        ( C)
        ( morphism-natural-numbers-object-Precat)
        ( succ-natural-numbers-object-Precat) ＝
      comp-hom-Precat (C) (f) (morphism-natural-numbers-object-Precat)
    morphism-natural-numbers-object-Precat-succ-comm =
      pr2 (pr2 (pr1 (pr2 (pr2 (pr2 nno)) x q f)))

    is-unique-morphism-natural-numbers-object-Precat :
      (u' : type-hom-Precat C object-natural-numbers-object-Precat x) →
      comp-hom-Precat C u' zero-natural-numbers-object-Precat ＝ q →
      comp-hom-Precat C u' succ-natural-numbers-object-Precat ＝
      comp-hom-Precat C f u' →
      morphism-natural-numbers-object-Precat ＝ u'
    is-unique-morphism-natural-numbers-object-Precat u' α β =
      ap pr1 (pr2 (pr2 (pr2 (pr2 nno)) x q f) (u' , α , β))
```
