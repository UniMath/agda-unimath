# Composition operations on binary families of sets

```agda
module category-theory.composition-operations-on-binary-families-of-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Given a type `A`, a **composition operation on a binary family of sets**
`hom : A → A → Set ` is a map

```text
  hom y z → hom x y → hom x z
```

for every triple of elements `x y z : A`.

For such operations, we can consider
[properties](foundation-core.propositions.md) such as **associativity** and
**unitality**.

## Definitions

### Composition operations in binary families of sets

```agda
module _
  {l1 l2 : Level} {A : UU l1} (hom-set : A → A → Set l2)
  where

  composition-operation-binary-family-Set : UU (l1 ⊔ l2)
  composition-operation-binary-family-Set =
    {x y z : A} →
    type-Set (hom-set y z) → type-Set (hom-set x y) → type-Set (hom-set x z)
```

### Associative composition operations in binary families of sets

```agda
module _
  {l1 l2 : Level} {A : UU l1} (hom-set : A → A → Set l2)
  where

  is-associative-composition-operation-binary-family-Set :
    composition-operation-binary-family-Set hom-set → UU (l1 ⊔ l2)
  is-associative-composition-operation-binary-family-Set comp-hom =
    {x y z w : A}
    (h : type-Set (hom-set z w))
    (g : type-Set (hom-set y z))
    (f : type-Set (hom-set x y)) →
    comp-hom (comp-hom h g) f ＝ comp-hom h (comp-hom g f)

  associative-composition-operation-binary-family-Set : UU (l1 ⊔ l2)
  associative-composition-operation-binary-family-Set =
    Σ ( composition-operation-binary-family-Set hom-set)
      ( is-associative-composition-operation-binary-family-Set)
```

### Unital composition operations in binary families of sets

```agda
module _
  {l1 l2 : Level} {A : UU l1} (hom-set : A → A → Set l2)
  where

  is-unital-composition-operation-binary-family-Set :
    composition-operation-binary-family-Set hom-set → UU (l1 ⊔ l2)
  is-unital-composition-operation-binary-family-Set comp-hom =
    Σ ( (x : A) → type-Set (hom-set x x))
      ( λ e →
        ( {x y : A} (f : type-Set (hom-set x y)) → comp-hom (e y) f ＝ f) ×
        ( {x y : A} (f : type-Set (hom-set x y)) → comp-hom f (e x) ＝ f))
```

## Properties

### Being associative is a property of composition operations in binary families of sets

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (hom-set : A → A → Set l2)
  (comp-hom : composition-operation-binary-family-Set hom-set)
  where
  is-prop-is-associative-composition-operation-binary-family-Set :
    is-prop
      ( is-associative-composition-operation-binary-family-Set hom-set comp-hom)
  is-prop-is-associative-composition-operation-binary-family-Set =
    is-prop-iterated-implicit-Π 4
      ( λ x y z w →
        is-prop-iterated-Π 3
          ( λ h g f →
            is-set-type-Set
              ( hom-set x w)
              ( comp-hom (comp-hom h g) f)
              ( comp-hom h (comp-hom g f))))

  is-associative-prop-composition-operation-binary-family-Set : Prop (l1 ⊔ l2)
  pr1 is-associative-prop-composition-operation-binary-family-Set =
    is-associative-composition-operation-binary-family-Set hom-set comp-hom
  pr2 is-associative-prop-composition-operation-binary-family-Set =
    is-prop-is-associative-composition-operation-binary-family-Set
```

### Being unital is a property of composition operations in binary families of sets

**Proof:** Suppose `e e' : (x : A) → hom-set x x` are both right and left units
with regard to composition. It is enough to show that `e ＝ e'` since the right
and left unit laws are propositions (because all hom-types are sets). By
function extensionality, it is enough to show that `e x ＝ e' x` for all
`x : A`. But by the unit laws we have the following chain of equalities:
`e x ＝ (e' x) ∘ (e x) ＝ e' x.`

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (hom-set : A → A → Set l2)
  (comp-hom : composition-operation-binary-family-Set hom-set)
  where

  abstract
    all-elements-equal-is-unital-composition-operation-binary-family-Set :
      all-elements-equal
        ( is-unital-composition-operation-binary-family-Set hom-set comp-hom)
    all-elements-equal-is-unital-composition-operation-binary-family-Set
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

  abstract
    is-prop-is-unital-composition-operation-binary-family-Set :
      is-prop
        ( is-unital-composition-operation-binary-family-Set hom-set comp-hom)
    is-prop-is-unital-composition-operation-binary-family-Set =
      is-prop-all-elements-equal
        all-elements-equal-is-unital-composition-operation-binary-family-Set

  is-unital-prop-composition-operation-binary-family-Set : Prop (l1 ⊔ l2)
  pr1 is-unital-prop-composition-operation-binary-family-Set =
    is-unital-composition-operation-binary-family-Set hom-set comp-hom
  pr2 is-unital-prop-composition-operation-binary-family-Set =
    is-prop-is-unital-composition-operation-binary-family-Set
```

## See also

- [Set-magmoids](category-theory.set-magmoids.md) capture the structure of
  composition operations on binary families of sets.

- [Precategories](category-theory.precategories.md) are associative and unital
  composition operations on binary families of sets.
- [Nonunital precategories](category-theory.nonunital-precategories.md) are
  associative composition operations on binary families of sets.
