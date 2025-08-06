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
open import foundation.strictly-involutive-identity-types
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Given a type `A`, a
{{#concept "composition operation" Disambiguation="on binary families of sets" Agda=composition-operation-binary-family-Set}}
on a binary family of [sets](foundation-core.sets.md) `hom : A → A → Set` is a
map

```text
  _∘_ : hom y z → hom x y → hom x z
```

for every triple of elements `x y z : A`.

For such operations, we can consider
[properties](foundation-core.propositions.md) such as _associativity_ and
_unitality_.

## Definitions

### Composition operations on binary families of sets

```agda
module _
  {l1 l2 : Level} {A : UU l1} (hom-set : A → A → Set l2)
  where

  composition-operation-binary-family-Set : UU (l1 ⊔ l2)
  composition-operation-binary-family-Set =
    {x y z : A} →
    type-Set (hom-set y z) → type-Set (hom-set x y) → type-Set (hom-set x z)
```

### Associative composition operations on binary families of sets

A composition operation

```text
  _∘_ : hom y z → hom x y → hom x z
```

on a binary family of sets of morphisms is called
{{#concept "associative" Disambiguation="composition operation on a binary family of sets" Agda=is-associative-composition-operation-binary-family-Set}}
if, for every triple of composable morphisms we have

```text
  (h ∘ g) ∘ f ＝ h ∘ (g ∘ f).
```

We give a slightly nonstandard definition of associativity using the
[strictly involutive identity types](foundation.strictly-involutive-identity-types.md)
rather than the standard [identity types](foundation-core.identity-types.md).
This is because, while the strictly involutive identity types are always
[equivalent](foundation-core.equivalences.md) to the standard ones, they satisfy
the strict computation rule `inv (inv p) ≐ p` which is practical in defining the
[opposite category](category-theory.opposite-categories.md), as this also makes
the opposite construction strictly involutive: `(𝒞ᵒᵖ)ᵒᵖ ≐ 𝒞`.

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
    ( comp-hom (comp-hom h g) f ＝ⁱ comp-hom h (comp-hom g f))

  associative-composition-operation-binary-family-Set : UU (l1 ⊔ l2)
  associative-composition-operation-binary-family-Set =
    Σ ( composition-operation-binary-family-Set hom-set)
      ( is-associative-composition-operation-binary-family-Set)

module _
  {l1 l2 : Level} {A : UU l1} (hom-set : A → A → Set l2)
  (H : associative-composition-operation-binary-family-Set hom-set)
  where

  comp-hom-associative-composition-operation-binary-family-Set :
    composition-operation-binary-family-Set hom-set
  comp-hom-associative-composition-operation-binary-family-Set = pr1 H

  involutive-eq-associative-composition-operation-binary-family-Set :
    {x y z w : A}
    (h : type-Set (hom-set z w))
    (g : type-Set (hom-set y z))
    (f : type-Set (hom-set x y)) →
    ( comp-hom-associative-composition-operation-binary-family-Set
      ( comp-hom-associative-composition-operation-binary-family-Set h g)
      ( f)) ＝ⁱ
    ( comp-hom-associative-composition-operation-binary-family-Set
      ( h)
      ( comp-hom-associative-composition-operation-binary-family-Set g f))
  involutive-eq-associative-composition-operation-binary-family-Set = pr2 H

  witness-associative-composition-operation-binary-family-Set :
    {x y z w : A}
    (h : type-Set (hom-set z w))
    (g : type-Set (hom-set y z))
    (f : type-Set (hom-set x y)) →
    ( comp-hom-associative-composition-operation-binary-family-Set
      ( comp-hom-associative-composition-operation-binary-family-Set h g) (f)) ＝
    ( comp-hom-associative-composition-operation-binary-family-Set
      ( h) (comp-hom-associative-composition-operation-binary-family-Set g f))
  witness-associative-composition-operation-binary-family-Set h g f =
    eq-involutive-eq
      ( involutive-eq-associative-composition-operation-binary-family-Set h g f)

  inv-witness-associative-composition-operation-binary-family-Set :
    {x y z w : A}
    (h : type-Set (hom-set z w))
    (g : type-Set (hom-set y z))
    (f : type-Set (hom-set x y)) →
    ( comp-hom-associative-composition-operation-binary-family-Set
      ( h) (comp-hom-associative-composition-operation-binary-family-Set g f)) ＝
    ( comp-hom-associative-composition-operation-binary-family-Set
      ( comp-hom-associative-composition-operation-binary-family-Set h g) (f))
  inv-witness-associative-composition-operation-binary-family-Set h g f =
    eq-involutive-eq
      ( invⁱ
        ( involutive-eq-associative-composition-operation-binary-family-Set
          ( h)
          ( g)
          ( f)))
```

### Unital composition operations on binary families of sets

A composition operation

```text
  _∘_ : hom y z → hom x y → hom x z
```

on a binary family of sets of morphisms is called
{{#concept "unital" Disambiguation="composition operation on a binary family of sets" Agda=is-unital-composition-operation-binary-family-Set}}
if there is a morphism `id_x : hom x x` for every element `x : A` such that

```text
  id_y ∘ f ＝ f   and f ∘ id_x = f.
```

As will be demonstrated momentarily, every composition operation on a binary
family of sets is unital in [at most one](foundation.subterminal-types.md) way.

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

### Being associative is a property of composition operations on binary families of sets

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
            is-prop-equiv
              ( equiv-eq-involutive-eq)
              ( is-set-type-Set
                ( hom-set x w)
                ( comp-hom (comp-hom h g) f)
                ( comp-hom h (comp-hom g f)))))

  is-associative-prop-composition-operation-binary-family-Set : Prop (l1 ⊔ l2)
  pr1 is-associative-prop-composition-operation-binary-family-Set =
    is-associative-composition-operation-binary-family-Set hom-set comp-hom
  pr2 is-associative-prop-composition-operation-binary-family-Set =
    is-prop-is-associative-composition-operation-binary-family-Set
```

### Being unital is a property of composition operations on binary families of sets

**Proof:** Suppose `e e' : (x : A) → hom x x` are both two-sided units with
respect to composition. It is enough to show that `e ＝ e'` since the right and
left unit laws are propositions by the set-condition on hom-types. By function
extensionality, it is enough to show that `e x ＝ e' x` for all `x : A`, and by
the unit laws we have:

```text
  e x ＝ (e' x) ∘ (e x) ＝ e' x. ∎
```

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
          product-Prop
            ( implicit-Π-Prop A
              ( λ a →
                implicit-Π-Prop A
                ( λ b →
                  Π-Prop
                    ( type-Set (hom-set a b))
                    ( λ f' → Id-Prop (hom-set a b) (comp-hom (x b) f') f'))))
            ( implicit-Π-Prop A
              ( λ a →
                implicit-Π-Prop A
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
- [Precategories](category-theory.precategories.md) are the structure of an
  associative and unital composition operation on a binary families of sets.
- [Nonunital precategories](category-theory.nonunital-precategories.md) are the
  structure of an associative composition operation on a binary families of
  sets.
