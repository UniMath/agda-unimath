# Composition operations on binary families of sets

```agda
module category-theory.composition-operations-on-binary-families-of-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **nonunital precategory** is a [precategory](category-theory.precategories.md)
that may not have identity maps. Such an object may also rightfully be called a
_semiprecategory_.

## Definition

### Composition operations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (hom-set : A → A → Set l2)
  where

  composition-operation-Set : UU (l1 ⊔ l2)
  composition-operation-Set =
    {x y z : A} →
    type-Set (hom-set y z) → type-Set (hom-set x y) → type-Set (hom-set x z)
```

### Associative composition operations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (hom-set : A → A → Set l2)
  where

  is-associative-composition-operation-Set :
    composition-operation-Set hom-set → UU (l1 ⊔ l2)
  is-associative-composition-operation-Set comp-hom =
    {x y z w : A}
    (h : type-Set (hom-set z w))
    (g : type-Set (hom-set y z))
    (f : type-Set (hom-set x y)) →
    comp-hom (comp-hom h g) f ＝ comp-hom h (comp-hom g f)

  associative-composition-structure-Set : UU (l1 ⊔ l2)
  associative-composition-structure-Set =
    Σ ( composition-operation-Set hom-set)
      ( is-associative-composition-operation-Set)
```

### Unital composition operations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (hom-set : A → A → Set l2)
  where

  is-unital-composition-operation-Set :
    composition-operation-Set hom-set → UU (l1 ⊔ l2)
  is-unital-composition-operation-Set comp-hom =
    Σ ( (x : A) → type-Set (hom-set x x))
      ( λ e →
        ( {x y : A} (f : type-Set (hom-set x y)) → comp-hom (e y) f ＝ f) ×
        ( {x y : A} (f : type-Set (hom-set x y)) → comp-hom f (e x) ＝ f))
```

## Properties

### Being associative is a property of composition operations in sets

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (hom-set : A → A → Set l2) (comp-hom : composition-operation-Set hom-set)
  where

  associativity-prop-composition-operation-Set : Prop (l1 ⊔ l2)
  associativity-prop-composition-operation-Set =
    Π-Prop' A
    ( λ x →
      Π-Prop' A
      ( λ y →
        Π-Prop' A
        ( λ z →
          Π-Prop' A
          ( λ w →
            Π-Prop
            ( type-Set (hom-set z w))
            ( λ h →
              Π-Prop
              ( type-Set (hom-set y z))
              ( λ g →
                Π-Prop
                ( type-Set (hom-set x y))
                ( λ f →
                  Id-Prop
                    ( hom-set x w)
                    ( comp-hom (comp-hom h g) f)
                    ( comp-hom h (comp-hom g f)))))))))

  is-prop-is-associative-composition-operation-Set :
    is-prop (is-associative-composition-operation-Set hom-set comp-hom)
  is-prop-is-associative-composition-operation-Set =
    is-prop-type-Prop associativity-prop-composition-operation-Set
```

### Being unital is a property of composition operations in sets

Suppose `e e' : (x : A) → hom-set x x` are both right and left units with regard
to composition. It is enough to show that `e = e'` since the right and left unit
laws are propositions (because all hom-types are sets). By function
extensionality, it is enough to show that `e x = e' x` for all `x : A`. But by
the unit laws we have the following chain of equalities:
`e x = (e' x) ∘ (e x) = e' x.`

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (hom-set : A → A → Set l2)
  ( comp-hom : composition-operation-Set hom-set)
  where

  abstract
    all-elements-equal-is-unital-composition-operation-Set :
      all-elements-equal (is-unital-composition-operation-Set hom-set comp-hom)
    all-elements-equal-is-unital-composition-operation-Set
      ( e , left-unit-law-e , right-unit-law-e)
      ( e' , left-unit-law-e' , right-unit-law-e') =
      eq-type-subtype
        ( λ x →
          prod-Prop
            ( Π-Prop' A
              ( λ a →
                Π-Prop' A
                  ( λ b →
                    Π-Prop
                      ( type-Set (hom-set a b))
                      ( λ f' → Id-Prop (hom-set a b) (comp-hom (x b) f') f'))))
            ( Π-Prop' A
              ( λ a →
                Π-Prop' A
                  ( λ b →
                    Π-Prop
                      ( type-Set (hom-set a b))
                      ( λ f' → Id-Prop (hom-set a b) (comp-hom f' (x a)) f')))))
        ( eq-htpy
          ( λ x → inv (left-unit-law-e' (e x)) ∙ right-unit-law-e (e' x)))

    is-prop-is-unital-composition-operation-Set :
      is-prop (is-unital-composition-operation-Set hom-set comp-hom)
    is-prop-is-unital-composition-operation-Set =
      is-prop-all-elements-equal
        all-elements-equal-is-unital-composition-operation-Set

    is-unital-prop-composition-operation-Set : Prop (l1 ⊔ l2)
    pr1 is-unital-prop-composition-operation-Set =
      is-unital-composition-operation-Set hom-set comp-hom
    pr2 is-unital-prop-composition-operation-Set =
      is-prop-is-unital-composition-operation-Set
```
