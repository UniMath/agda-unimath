# Maps between precategories

```agda
module category-theory.maps-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.maps-set-magmoids
open import category-theory.precategories

open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
```

</details>

## Idea

A **map** from a [precategory](category-theory.precategories.md) `C` to a
precategory `D` consists of:

- a map `F₀ : C → D` on objects,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms

## Definitions

### Maps between precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  map-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  map-Precategory =
    map-Set-Magmoid
      ( set-magmoid-Precategory C)
      ( set-magmoid-Precategory D)

  obj-map-Precategory :
    (F : map-Precategory) → obj-Precategory C → obj-Precategory D
  obj-map-Precategory =
    obj-map-Set-Magmoid
      ( set-magmoid-Precategory C)
      ( set-magmoid-Precategory D)

  hom-map-Precategory :
    (F : map-Precategory)
    {x y : obj-Precategory C} →
    hom-Precategory C x y →
    hom-Precategory D
      ( obj-map-Precategory F x)
      ( obj-map-Precategory F y)
  hom-map-Precategory =
    hom-map-Set-Magmoid
      ( set-magmoid-Precategory C)
      ( set-magmoid-Precategory D)
```

## Properties

### Computing transport in the hom-family

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  {x x' y y' : obj-Precategory C}
  where

  compute-binary-tr-hom-Precategory :
    (p : x ＝ x') (q : y ＝ y') (f : hom-Precategory C x y) →
    ( comp-hom-Precategory C
      ( hom-eq-Precategory C y y' q)
      ( comp-hom-Precategory C f (hom-inv-eq-Precategory C x x' p))) ＝
    ( binary-tr (hom-Precategory C) p q f)
  compute-binary-tr-hom-Precategory refl refl f =
    ( left-unit-law-comp-hom-Precategory C
      ( comp-hom-Precategory C f (id-hom-Precategory C))) ∙
    ( right-unit-law-comp-hom-Precategory C f)

  naturality-binary-tr-hom-Precategory :
    (p : x ＝ x') (q : y ＝ y')
    (f : hom-Precategory C x y) →
    ( coherence-square-hom-Precategory C
      ( f)
      ( hom-eq-Precategory C x x' p)
      ( hom-eq-Precategory C y y' q)
      ( binary-tr (hom-Precategory C) p q f))
  naturality-binary-tr-hom-Precategory refl refl f =
    ( right-unit-law-comp-hom-Precategory C f) ∙
    ( inv (left-unit-law-comp-hom-Precategory C f))

  naturality-binary-tr-hom-Precategory' :
    (p : x ＝ x') (q : y ＝ y')
    (f : hom-Precategory C x y) →
    ( coherence-square-hom-Precategory C
      ( hom-eq-Precategory C x x' p)
      ( f)
      ( binary-tr (hom-Precategory C) p q f)
      ( hom-eq-Precategory C y y' q))
  naturality-binary-tr-hom-Precategory' refl refl f =
    ( left-unit-law-comp-hom-Precategory C f) ∙
    ( inv (right-unit-law-comp-hom-Precategory C f))
```

### Characterization of equality of maps between precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  coherence-htpy-map-Precategory :
    (f g : map-Precategory C D) →
    obj-map-Precategory C D f ~ obj-map-Precategory C D g →
    UU (l1 ⊔ l2 ⊔ l4)
  coherence-htpy-map-Precategory f g H =
    {x y : obj-Precategory C}
    (a : hom-Precategory C x y) →
    coherence-square-hom-Precategory D
      ( hom-map-Precategory C D f a)
      ( hom-eq-Precategory D
        ( obj-map-Precategory C D f x)
        ( obj-map-Precategory C D g x)
        ( H x))
      ( hom-eq-Precategory D
        ( obj-map-Precategory C D f y)
        ( obj-map-Precategory C D g y)
        ( H y))
      ( hom-map-Precategory C D g a)

  htpy-map-Precategory :
    (f g : map-Precategory C D) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-map-Precategory f g =
    Σ ( obj-map-Precategory C D f ~ obj-map-Precategory C D g)
      ( coherence-htpy-map-Precategory f g)

  refl-htpy-map-Precategory :
    (f : map-Precategory C D) → htpy-map-Precategory f f
  pr1 (refl-htpy-map-Precategory f) = refl-htpy
  pr2 (refl-htpy-map-Precategory f) a =
    naturality-binary-tr-hom-Precategory D
      ( refl)
      ( refl)
      ( hom-map-Precategory C D f a)

  htpy-eq-map-Precategory :
    (f g : map-Precategory C D) → f ＝ g → htpy-map-Precategory f g
  htpy-eq-map-Precategory f .f refl = refl-htpy-map-Precategory f

  is-torsorial-htpy-map-Precategory :
    (f : map-Precategory C D) → is-torsorial (htpy-map-Precategory f)
  is-torsorial-htpy-map-Precategory f =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (obj-map-Precategory C D f))
      ( obj-map-Precategory C D f , refl-htpy)
      ( is-torsorial-Eq-implicit-Π
        ( λ x →
          is-torsorial-Eq-implicit-Π
            ( λ y →
              is-contr-equiv
                ( Σ
                  ( (a : hom-Precategory C x y) →
                    hom-Precategory D
                      ( obj-map-Precategory C D f x)
                      ( obj-map-Precategory C D f y))
                  ( _~ hom-map-Precategory C D f))
                ( equiv-tot
                  ( λ g₁ →
                    equiv-binary-concat-htpy
                      ( inv-htpy (right-unit-law-comp-hom-Precategory D ∘ g₁))
                      ( left-unit-law-comp-hom-Precategory D ∘
                        hom-map-Precategory C D f)))
                ( is-torsorial-htpy' (hom-map-Precategory C D f)))))

  is-equiv-htpy-eq-map-Precategory :
    (f g : map-Precategory C D) → is-equiv (htpy-eq-map-Precategory f g)
  is-equiv-htpy-eq-map-Precategory f =
    fundamental-theorem-id
      ( is-torsorial-htpy-map-Precategory f)
      ( htpy-eq-map-Precategory f)

  equiv-htpy-eq-map-Precategory :
    (f g : map-Precategory C D) → (f ＝ g) ≃ htpy-map-Precategory f g
  pr1 (equiv-htpy-eq-map-Precategory f g) = htpy-eq-map-Precategory f g
  pr2 (equiv-htpy-eq-map-Precategory f g) = is-equiv-htpy-eq-map-Precategory f g

  eq-htpy-map-Precategory :
    (f g : map-Precategory C D) → htpy-map-Precategory f g → f ＝ g
  eq-htpy-map-Precategory f g =
    map-inv-equiv (equiv-htpy-eq-map-Precategory f g)
```

## See also

- [Functors between precategories](category-theory.functors-precategories.md)
- [The precategory of maps and natural transformations between precategories](category-theory.precategory-of-maps-precategories.md)
