# Copresheaf categories

```agda
module category-theory.copresheaf-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.category-of-functors-from-small-to-large-categories
open import category-theory.constant-functors
open import category-theory.functors-from-small-to-large-precategories
open import category-theory.functors-precategories
open import category-theory.initial-objects-precategories
open import category-theory.large-categories
open import category-theory.large-precategories
open import category-theory.natural-transformations-functors-from-small-to-large-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories
open import category-theory.precategory-of-functors-from-small-to-large-precategories
open import category-theory.terminal-objects-precategories

open import foundation.category-of-sets
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

Given a [precategory](category-theory.precategories.md) `C`, we can form its
**copresheaf [category](category-theory.large-categories.md)** as the
[large category of functors](category-theory.functors-from-small-to-large-precategories.md)
from `C`, into the [large category of sets](foundation.category-of-sets.md)

```text
  C → Set.
```

To this large category, there is an associated
[small category](category-theory.categories.md) of small copresheaves, taking
values in small [sets](foundation-core.sets.md).

## Definitions

### The large category of copresheaves on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  copresheaf-large-precategory-Precategory :
    Large-Precategory (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l l' → l1 ⊔ l2 ⊔ l ⊔ l')
  copresheaf-large-precategory-Precategory =
    functor-large-precategory-Small-Large-Precategory C Set-Large-Precategory

  is-large-category-copresheaf-large-category-Precategory :
    is-large-category-Large-Precategory copresheaf-large-precategory-Precategory
  is-large-category-copresheaf-large-category-Precategory =
    is-large-category-functor-large-precategory-is-large-category-Small-Large-Precategory
      ( C)
      ( Set-Large-Precategory)
      ( is-large-category-Set-Large-Precategory)

  copresheaf-large-category-Precategory :
    Large-Category (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l l' → l1 ⊔ l2 ⊔ l ⊔ l')
  large-precategory-Large-Category copresheaf-large-category-Precategory =
    copresheaf-large-precategory-Precategory
  is-large-category-Large-Category copresheaf-large-category-Precategory =
    is-large-category-copresheaf-large-category-Precategory

  copresheaf-Precategory :
    (l : Level) → UU (l1 ⊔ l2 ⊔ lsuc l)
  copresheaf-Precategory =
    obj-Large-Precategory copresheaf-large-precategory-Precategory

  module _
    {l : Level} (P : copresheaf-Precategory l)
    where

    element-set-copresheaf-Precategory : obj-Precategory C → Set l
    element-set-copresheaf-Precategory =
      obj-functor-Small-Large-Precategory C Set-Large-Precategory P

    element-copresheaf-Precategory : obj-Precategory C → UU l
    element-copresheaf-Precategory X =
      type-Set (element-set-copresheaf-Precategory X)

    action-copresheaf-Precategory :
      {X Y : obj-Precategory C} →
      hom-Precategory C X Y →
      element-copresheaf-Precategory X → element-copresheaf-Precategory Y
    action-copresheaf-Precategory f =
      hom-functor-Small-Large-Precategory C Set-Large-Precategory P f

    preserves-id-action-copresheaf-Precategory :
      {X : obj-Precategory C} →
      action-copresheaf-Precategory {X} {X} (id-hom-Precategory C) ~ id
    preserves-id-action-copresheaf-Precategory =
      htpy-eq
        ( preserves-id-functor-Small-Large-Precategory C
          ( Set-Large-Precategory)
          ( P)
          ( _))

    preserves-comp-action-copresheaf-Precategory :
      {X Y Z : obj-Precategory C}
      (g : hom-Precategory C Y Z) (f : hom-Precategory C X Y) →
      action-copresheaf-Precategory (comp-hom-Precategory C g f) ~
      action-copresheaf-Precategory g ∘ action-copresheaf-Precategory f
    preserves-comp-action-copresheaf-Precategory g f =
      htpy-eq
        ( preserves-comp-functor-Small-Large-Precategory C
          ( Set-Large-Precategory)
          ( P)
          ( g)
          ( f))

  hom-set-copresheaf-Precategory :
    {l3 l4 : Level}
    (P : copresheaf-Precategory l3)
    (Q : copresheaf-Precategory l4) → Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-set-copresheaf-Precategory =
    hom-set-Large-Precategory copresheaf-large-precategory-Precategory

  hom-copresheaf-Precategory :
    {l3 l4 : Level}
    (X : copresheaf-Precategory l3) (Y : copresheaf-Precategory l4) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-copresheaf-Precategory =
    hom-Large-Precategory copresheaf-large-precategory-Precategory

  module _
    {l3 l4 : Level}
    (P : copresheaf-Precategory l3) (Q : copresheaf-Precategory l4)
    (h : hom-copresheaf-Precategory P Q)
    where

    map-hom-copresheaf-Precategory :
      (X : obj-Precategory C) →
      element-copresheaf-Precategory P X → element-copresheaf-Precategory Q X
    map-hom-copresheaf-Precategory =
      hom-natural-transformation-Small-Large-Precategory C
        ( Set-Large-Precategory)
        ( P)
        ( Q)
        ( h)

    naturality-hom-copresheaf-Precategory :
      {X Y : obj-Precategory C} (f : hom-Precategory C X Y) →
      coherence-square-maps
        ( action-copresheaf-Precategory P f)
        ( map-hom-copresheaf-Precategory X)
        ( map-hom-copresheaf-Precategory Y)
        ( action-copresheaf-Precategory Q f)
    naturality-hom-copresheaf-Precategory f =
      htpy-eq
        ( naturality-natural-transformation-Small-Large-Precategory C
          ( Set-Large-Precategory)
          ( P)
          ( Q)
          ( h)
          ( f))

  comp-hom-copresheaf-Precategory :
    {l3 l4 l5 : Level}
    (X : copresheaf-Precategory l3)
    (Y : copresheaf-Precategory l4)
    (Z : copresheaf-Precategory l5) →
    hom-copresheaf-Precategory Y Z →
    hom-copresheaf-Precategory X Y →
    hom-copresheaf-Precategory X Z
  comp-hom-copresheaf-Precategory X Y Z =
    comp-hom-Large-Precategory
      ( copresheaf-large-precategory-Precategory)
      { X = X}
      { Y}
      { Z}

  id-hom-copresheaf-Precategory :
    {l3 : Level} (X : copresheaf-Precategory l3) →
    hom-copresheaf-Precategory X X
  id-hom-copresheaf-Precategory X =
    id-hom-Large-Precategory copresheaf-large-precategory-Precategory {X = X}

  associative-comp-hom-copresheaf-Precategory :
    {l3 l4 l5 l6 : Level}
    (X : copresheaf-Precategory l3)
    (Y : copresheaf-Precategory l4)
    (Z : copresheaf-Precategory l5)
    (W : copresheaf-Precategory l6)
    (h : hom-copresheaf-Precategory Z W)
    (g : hom-copresheaf-Precategory Y Z)
    (f : hom-copresheaf-Precategory X Y) →
    comp-hom-copresheaf-Precategory X Y W
      ( comp-hom-copresheaf-Precategory Y Z W h g)
      ( f) ＝
    comp-hom-copresheaf-Precategory X Z W
      ( h)
      ( comp-hom-copresheaf-Precategory X Y Z g f)
  associative-comp-hom-copresheaf-Precategory X Y Z W =
    associative-comp-hom-Large-Precategory
      ( copresheaf-large-precategory-Precategory)
      { X = X}
      { Y}
      { Z}
      { W}

  left-unit-law-comp-hom-copresheaf-Precategory :
    {l3 l4 : Level}
    (X : copresheaf-Precategory l3)
    (Y : copresheaf-Precategory l4)
    (f : hom-copresheaf-Precategory X Y) →
    comp-hom-copresheaf-Precategory X Y Y
      ( id-hom-copresheaf-Precategory Y)
      ( f) ＝
    f
  left-unit-law-comp-hom-copresheaf-Precategory X Y =
    left-unit-law-comp-hom-Large-Precategory
      ( copresheaf-large-precategory-Precategory)
      { X = X}
      { Y}

  right-unit-law-comp-hom-copresheaf-Precategory :
    {l3 l4 : Level}
    (X : copresheaf-Precategory l3)
    (Y : copresheaf-Precategory l4)
    (f : hom-copresheaf-Precategory X Y) →
    comp-hom-copresheaf-Precategory X X Y
      ( f)
      ( id-hom-copresheaf-Precategory X) ＝
    f
  right-unit-law-comp-hom-copresheaf-Precategory X Y =
    right-unit-law-comp-hom-Large-Precategory
      ( copresheaf-large-precategory-Precategory)
      { X = X}
      { Y}
```

### The category of small copresheaves on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (l : Level)
  where

  copresheaf-category-Precategory :
    Category (l1 ⊔ l2 ⊔ lsuc l) (l1 ⊔ l2 ⊔ l)
  copresheaf-category-Precategory =
    category-Large-Category (copresheaf-large-category-Precategory C) l

  copresheaf-precategory-Precategory :
    Precategory (l1 ⊔ l2 ⊔ lsuc l) (l1 ⊔ l2 ⊔ l)
  copresheaf-precategory-Precategory =
    precategory-Large-Precategory (copresheaf-large-precategory-Precategory C) l
```

### The product of small copresheaves

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2)
  where

  product-hom-copresheaf-Precategory :
    copresheaf-Precategory C l3 →
    copresheaf-Precategory C l4 →
    copresheaf-Precategory C (l3 ⊔ l4)
  pr1 (product-hom-copresheaf-Precategory F G) x =
    product-Set
      ( obj-functor-Precategory C (Set-Precategory l3) F x)
      ( obj-functor-Precategory C (Set-Precategory l4) G x)
  pr1 (pr2 (product-hom-copresheaf-Precategory F G)) f =
    map-product
      ( hom-functor-Precategory C (Set-Precategory l3) F f)
      ( hom-functor-Precategory C (Set-Precategory l4) G f)
  pr1 (pr2 (pr2 (product-hom-copresheaf-Precategory F G))) g f =
    eq-htpy
      ( λ w →
        eq-pair
          ( htpy-eq
            ( preserves-comp-functor-Precategory C (Set-Precategory l3)
              F g f)
            ( pr1 w))
          ( htpy-eq
            ( preserves-comp-functor-Precategory C (Set-Precategory l4)
              G g f)
            ( pr2 w)))
  pr2 (pr2 (pr2 (product-hom-copresheaf-Precategory F G))) x =
    eq-htpy
      ( λ w →
        eq-pair
          ( htpy-eq
            ( preserves-id-functor-Precategory C (Set-Precategory l3)
              F x)
            ( pr1 w))
          ( htpy-eq
            ( preserves-id-functor-Precategory C (Set-Precategory l4)
              G x)
            ( pr2 w)))
```

### The initial copresheaf

Since colimits are computed pointwise, the initial copresheaf is the constant
functor at the empty set.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (l : Level)
  where

  obj-initial-copresheaf-Precategory :
    copresheaf-Precategory C l
  obj-initial-copresheaf-Precategory =
    constant-functor-Precategory
      C (Set-Precategory l) (raise-empty-Set l)

  hom-initial-copresheaf-Precategory :
    ( X : copresheaf-Precategory C l) →
    hom-Precategory
      (copresheaf-precategory-Precategory C l)
      obj-initial-copresheaf-Precategory
      X
  pr1 (hom-initial-copresheaf-Precategory X) x (map-raise ())
  pr2 (hom-initial-copresheaf-Precategory X) f =
    eq-htpy (λ where (map-raise ()))

  is-unique-hom-initial-copresheaf-Precategory :
    ( X : copresheaf-Precategory C l) →
    ( τ :
      hom-Precategory
        (copresheaf-precategory-Precategory C l)
        obj-initial-copresheaf-Precategory
        X) →
    hom-initial-copresheaf-Precategory X ＝ τ
  is-unique-hom-initial-copresheaf-Precategory X τ =
    eq-htpy-hom-family-natural-transformation-Precategory
      ( C)
      ( Set-Precategory l)
      ( obj-initial-copresheaf-Precategory)
      ( X)
      ( hom-initial-copresheaf-Precategory X)
      ( τ)
      ( λ x → eq-htpy (λ where (map-raise ())))

  initial-copresheaf-Precategory :
    initial-obj-Precategory
      (copresheaf-precategory-Precategory C l)
  pr1 initial-copresheaf-Precategory =
    obj-initial-copresheaf-Precategory
  pr1 (pr2 initial-copresheaf-Precategory X) =
    hom-initial-copresheaf-Precategory X
  pr2 (pr2 initial-copresheaf-Precategory X) τ =
    is-unique-hom-initial-copresheaf-Precategory X τ
```

### The terminal copresheaf

Since limits are computed pointwise, the terminal copresheaf is the constant
functor at the terminal set.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (l : Level)
  where

  obj-terminal-copresheaf-Precategory :
    copresheaf-Precategory C l
  obj-terminal-copresheaf-Precategory =
    constant-functor-Precategory
      C (Set-Precategory l) (raise-unit-Set l)

  hom-terminal-copresheaf-Precategory :
    ( X : copresheaf-Precategory C l) →
    hom-Precategory
      (copresheaf-precategory-Precategory C l)
      X
      obj-terminal-copresheaf-Precategory
  pr1 (hom-terminal-copresheaf-Precategory X) c m = raise-star
  pr2 (hom-terminal-copresheaf-Precategory X) f = refl

  is-unique-hom-terminal-copresheaf-Precategory :
    ( X : copresheaf-Precategory C l) →
    ( τ :
      hom-Precategory
        (copresheaf-precategory-Precategory C l)
        X
        obj-terminal-copresheaf-Precategory) →
    hom-terminal-copresheaf-Precategory X ＝ τ
  is-unique-hom-terminal-copresheaf-Precategory X τ =
    eq-htpy-hom-family-natural-transformation-Precategory
      ( C)
      ( Set-Precategory l)
      ( X)
      ( obj-terminal-copresheaf-Precategory)
      ( hom-terminal-copresheaf-Precategory X)
      ( τ)
      ( λ x → eq-htpy (λ _ → eq-is-prop is-prop-raise-unit))

  terminal-copresheaf-Precategory :
    terminal-obj-Precategory
      (copresheaf-precategory-Precategory C l)
  pr1 terminal-copresheaf-Precategory =
    obj-terminal-copresheaf-Precategory
  pr1 (pr2 terminal-copresheaf-Precategory X) =
    hom-terminal-copresheaf-Precategory X
  pr2 (pr2 terminal-copresheaf-Precategory X) τ =
    is-unique-hom-terminal-copresheaf-Precategory X τ
```

## See also

- [The Yoneda lemma](category-theory.yoneda-lemma-precategories.md)

## External links

- [Presheaf precategories](https://1lab.dev/Cat.Functor.Base.html#presheaf-precategories)
  at 1lab
- [category of presheaves](https://ncatlab.org/nlab/show/category+of+presheaves)
  at $n$Lab
- [copresheaf](https://ncatlab.org/nlab/show/copresheaf) at $n$Lab
