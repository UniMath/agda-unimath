# Precategories

```agda
module category-theory.precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functions
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A precategory in Homotopy Type Theory consists of:
- a type `A` of objects,
- for each pair of objects `x y : A`, a set of morphisms `hom x y : Set`,
together with a composition operation `comp : hom y z → hom x y → hom x z` such that:
- `comp (comp h g) f = comp h (comp g f)` for any morphisms `h : hom z w`, `g : hom y z` and `f : hom x y`,
- for each object `x : A` there is a morphism `id_x : hom x x` such that `comp id_x f = f` and `comp g id_x = g` for any morphisms `f : hom x y` and `g : hom z x`.

The reason this is called a *pre*category and not a category in Homotopy Type Theory is that we want to reserve that name for precategories where the identities between the objects are exactly the isomorphisms.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} (hom : A → A → Set l2)
  where

  associative-composition-structure-Set : UU (l1 ⊔ l2)
  associative-composition-structure-Set =
    Σ ( {x y z : A}
        → type-Set (hom y z)
        → type-Set (hom x y)
        → type-Set (hom x z))
      ( λ μ →
        {x y z w : A} (h : type-Set (hom z w)) (g : type-Set (hom y z))
        (f : type-Set (hom x y)) → μ (μ h g) f ＝ μ h (μ g f))

  is-unital-composition-structure-Set :
    associative-composition-structure-Set → UU (l1 ⊔ l2)
  is-unital-composition-structure-Set μ =
    Σ ( (x : A) → type-Set (hom x x))
      ( λ e →
        ( {x y : A} (f : type-Set (hom x y)) → pr1 μ (e y) f ＝ f) ×
        ( {x y : A} (f : type-Set (hom x y)) → pr1 μ f (e x) ＝ f))

Precat :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Precat l1 l2 =
  Σ ( UU l1)
    ( λ A →
      Σ ( A → A → Set l2)
        ( λ hom →
          Σ ( associative-composition-structure-Set hom)
            ( is-unital-composition-structure-Set hom)))

module _
  {l1 l2 : Level} (C : Precat l1 l2)
  where

  obj-Precat : UU l1
  obj-Precat = pr1 C

  hom-Precat : (x y : obj-Precat) → Set l2
  hom-Precat = pr1 (pr2 C)

  type-hom-Precat : (x y : obj-Precat) → UU l2
  type-hom-Precat x y = type-Set (hom-Precat x y)

  is-set-type-hom-Precat : (x y : obj-Precat) → is-set (type-hom-Precat x y)
  is-set-type-hom-Precat x y = is-set-type-Set (hom-Precat x y)

  associative-composition-Precat :
    associative-composition-structure-Set hom-Precat
  associative-composition-Precat = pr1 (pr2 (pr2 C))

  comp-hom-Precat : {x y z : obj-Precat} →
    type-hom-Precat y z → type-hom-Precat x y → type-hom-Precat x z
  comp-hom-Precat = pr1 associative-composition-Precat

  comp-hom-Precat' : {x y z : obj-Precat} →
    type-hom-Precat x y → type-hom-Precat y z → type-hom-Precat x z
  comp-hom-Precat' f g = comp-hom-Precat g f

  precomp-hom-Precat :
    {x y : obj-Precat} (f : type-hom-Precat x y) (z : obj-Precat) →
    type-hom-Precat y z → type-hom-Precat x z
  precomp-hom-Precat f z g = comp-hom-Precat g f

  postcomp-hom-Precat :
    {x y : obj-Precat} (f : type-hom-Precat x y) (z : obj-Precat) →
    type-hom-Precat z x → type-hom-Precat z y
  postcomp-hom-Precat f z = comp-hom-Precat f

  assoc-comp-hom-Precat :
    {x y z w : obj-Precat} (h : type-hom-Precat z w) (g : type-hom-Precat y z)
    (f : type-hom-Precat x y) →
    ( comp-hom-Precat (comp-hom-Precat h g) f) ＝
    ( comp-hom-Precat h (comp-hom-Precat g f))
  assoc-comp-hom-Precat = pr2 associative-composition-Precat

  is-unital-Precat :
    is-unital-composition-structure-Set
      hom-Precat
      associative-composition-Precat
  is-unital-Precat = pr2 (pr2 (pr2 C))

  id-hom-Precat : {x : obj-Precat} → type-hom-Precat x x
  id-hom-Precat {x} = pr1 is-unital-Precat x

  left-unit-law-comp-hom-Precat :
    {x y : obj-Precat} (f : type-hom-Precat x y) →
    comp-hom-Precat id-hom-Precat f ＝ f
  left-unit-law-comp-hom-Precat = pr1 (pr2 is-unital-Precat)

  right-unit-law-comp-hom-Precat :
    {x y : obj-Precat} (f : type-hom-Precat x y) →
    comp-hom-Precat f id-hom-Precat ＝ f
  right-unit-law-comp-hom-Precat = pr2 (pr2 is-unital-Precat)
```

## Examples

### The category of sets and functions

The precategory of sets and functions in a given universe.

```agda
Set-Precat : (l : Level) → Precat (lsuc l) l
pr1 (Set-Precat l) = Set l
pr1 (pr2 (Set-Precat l)) = hom-Set
pr1 (pr1 (pr2 (pr2 (Set-Precat l)))) g f = g ∘ f
pr2 (pr1 (pr2 (pr2 (Set-Precat l)))) h g f = refl
pr1 (pr2 (pr2 (pr2 (Set-Precat l)))) x = id
pr1 (pr2 (pr2 (pr2 (pr2 (Set-Precat l))))) f = refl
pr2 (pr2 (pr2 (pr2 (pr2 (Set-Precat l))))) f = refl
```

## Properties

### The property of having identity morphisms is a proposition

Suppose `e e' : (x : A) → hom x x` are both right and left units with regard to `comp`. It is enough to show that `e = e'` since the right and left unit laws are propositions (because all hom-types are sets). By function extensionality, it is enough to show that `e x = e' x` for all `x : A`. But by the unit laws we have the following chain of equalities:
`e x = comp (e' x) (e x) = e' x.`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (hom : A → A → Set l2)
  where

  abstract
    all-elements-equal-is-unital-composition-structure-Set :
      ( μ : associative-composition-structure-Set hom) →
      all-elements-equal (is-unital-composition-structure-Set hom μ)
    all-elements-equal-is-unital-composition-structure-Set
      ( pair μ assoc-μ)
      ( pair e (pair left-unit-law-e right-unit-law-e))
      ( pair e' (pair left-unit-law-e' right-unit-law-e')) =
      eq-type-subtype
        ( λ x →
          prod-Prop
            ( Π-Prop' A
              ( λ a →
                Π-Prop' A
                  ( λ b →
                    Π-Prop
                      ( type-Set (hom a b))
                      ( λ f' →
                        Id-Prop (hom a b) (μ (x b) f') f'))))
            ( Π-Prop' A
              ( λ a →
                Π-Prop' A
                  ( λ b →
                    Π-Prop
                      ( type-Set (hom a b))
                      ( λ f' →
                        Id-Prop (hom a b) (μ f' (x a)) f')))))
        ( eq-htpy
          ( λ x →
            ( inv (left-unit-law-e' (e x))) ∙
            ( right-unit-law-e (e' x))))

    is-prop-is-unital-composition-structure-Set :
      ( μ : associative-composition-structure-Set hom) →
      is-prop (is-unital-composition-structure-Set hom μ)
    is-prop-is-unital-composition-structure-Set μ =
      is-prop-all-elements-equal
        ( all-elements-equal-is-unital-composition-structure-Set μ)
```
