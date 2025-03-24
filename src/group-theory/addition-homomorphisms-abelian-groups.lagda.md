# Pointwise addition of morphisms of abelian groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.addition-homomorphisms-abelian-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.universe-levels

open import group-theory.abelian-groups funext univalence truncations
open import group-theory.groups funext univalence truncations
open import group-theory.homomorphisms-abelian-groups funext univalence truncations
open import group-theory.semigroups funext univalence
```

</details>

## Idea

Morphisms of abelian groups can be added pointwise. This operation turns each
hom-set of abelian groups into an abelian group. Moreover, composition of
abelian groups distributes over addition from the left and from the right.

## Definition

### The abelian group of homomorphisms between two abelian groups

#### Pointwise operations on morphisms between abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  add-hom-Ab :
    hom-Ab A B → hom-Ab A B → hom-Ab A B
  pr1 (add-hom-Ab f g) x = add-Ab B (map-hom-Ab A B f x) (map-hom-Ab A B g x)
  pr2 (add-hom-Ab f g) {x} {y} =
    ( ap-add-Ab B
      ( preserves-add-hom-Ab A B f)
      ( preserves-add-hom-Ab A B g)) ∙
    ( interchange-add-add-Ab B
      ( map-hom-Ab A B f x)
      ( map-hom-Ab A B f y)
      ( map-hom-Ab A B g x)
      ( map-hom-Ab A B g y))

  zero-hom-Ab : hom-Ab A B
  pr1 zero-hom-Ab x = zero-Ab B
  pr2 zero-hom-Ab = inv (left-unit-law-add-Ab B (zero-Ab B))

  neg-hom-Ab : hom-Ab A B → hom-Ab A B
  pr1 (neg-hom-Ab f) x = neg-Ab B (map-hom-Ab A B f x)
  pr2 (neg-hom-Ab f) {x} {y} =
    ( ap (neg-Ab B) (preserves-add-hom-Ab A B f)) ∙
    ( distributive-neg-add-Ab B (map-hom-Ab A B f x) (map-hom-Ab A B f y))
```

#### Associativity of pointwise addition of morphisms of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  associative-add-hom-Ab :
    (f g h : hom-Ab A B) →
    add-hom-Ab A B (add-hom-Ab A B f g) h ＝
    add-hom-Ab A B f (add-hom-Ab A B g h)
  associative-add-hom-Ab f g h =
    eq-htpy-hom-Ab A B
      ( λ x →
        associative-add-Ab B
          ( map-hom-Ab A B f x)
          ( map-hom-Ab A B g x)
          ( map-hom-Ab A B h x))
```

#### Commutativity of pointwise addition of morphisms of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  commutative-add-hom-Ab :
    (f g : hom-Ab A B) → add-hom-Ab A B f g ＝ add-hom-Ab A B g f
  commutative-add-hom-Ab f g =
    eq-htpy-hom-Ab A B
      ( λ x → commutative-add-Ab B (map-hom-Ab A B f x) (map-hom-Ab A B g x))
```

#### Unit laws for pointwise addition of morphisms of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  left-unit-law-add-hom-Ab :
    (f : hom-Ab A B) → add-hom-Ab A B (zero-hom-Ab A B) f ＝ f
  left-unit-law-add-hom-Ab f =
    eq-htpy-hom-Ab A B (λ x → left-unit-law-add-Ab B (map-hom-Ab A B f x))

  right-unit-law-add-hom-Ab :
    (f : hom-Ab A B) → add-hom-Ab A B f (zero-hom-Ab A B) ＝ f
  right-unit-law-add-hom-Ab f =
    eq-htpy-hom-Ab A B (λ x → right-unit-law-add-Ab B (map-hom-Ab A B f x))
```

#### Inverse laws for pointwise addition of morphisms of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  left-inverse-law-add-hom-Ab :
    (f : hom-Ab A B) →
    add-hom-Ab A B (neg-hom-Ab A B f) f ＝ zero-hom-Ab A B
  left-inverse-law-add-hom-Ab f =
    eq-htpy-hom-Ab A B (λ x → left-inverse-law-add-Ab B (map-hom-Ab A B f x))

  right-inverse-law-add-hom-Ab :
    (f : hom-Ab A B) →
    add-hom-Ab A B f (neg-hom-Ab A B f) ＝ zero-hom-Ab A B
  right-inverse-law-add-hom-Ab f =
    eq-htpy-hom-Ab A B (λ x → right-inverse-law-add-Ab B (map-hom-Ab A B f x))
```

#### `hom G H` is an abelian group

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  semigroup-hom-Ab : Semigroup (l1 ⊔ l2)
  pr1 semigroup-hom-Ab = hom-set-Ab A B
  pr1 (pr2 semigroup-hom-Ab) = add-hom-Ab A B
  pr2 (pr2 semigroup-hom-Ab) = associative-add-hom-Ab A B

  group-hom-Ab : Group (l1 ⊔ l2)
  pr1 group-hom-Ab = semigroup-hom-Ab
  pr1 (pr1 (pr2 group-hom-Ab)) = zero-hom-Ab A B
  pr1 (pr2 (pr1 (pr2 group-hom-Ab))) = left-unit-law-add-hom-Ab A B
  pr2 (pr2 (pr1 (pr2 group-hom-Ab))) = right-unit-law-add-hom-Ab A B
  pr1 (pr2 (pr2 group-hom-Ab)) = neg-hom-Ab A B
  pr1 (pr2 (pr2 (pr2 group-hom-Ab))) = left-inverse-law-add-hom-Ab A B
  pr2 (pr2 (pr2 (pr2 group-hom-Ab))) = right-inverse-law-add-hom-Ab A B

  ab-hom-Ab : Ab (l1 ⊔ l2)
  pr1 ab-hom-Ab = group-hom-Ab
  pr2 ab-hom-Ab = commutative-add-hom-Ab A B
```

## Properties

### Distributivity of composition over pointwise addition of morphisms of abelian groups

```agda
module _
  {l1 l2 l3 : Level} (A : Ab l1) (B : Ab l2) (C : Ab l3)
  where

  left-distributive-comp-add-hom-Ab :
    (h : hom-Ab B C) (f g : hom-Ab A B) →
    comp-hom-Ab A B C h (add-hom-Ab A B f g) ＝
    add-hom-Ab A C (comp-hom-Ab A B C h f) (comp-hom-Ab A B C h g)
  left-distributive-comp-add-hom-Ab h f g =
    eq-htpy-hom-Ab A C (λ x → preserves-add-hom-Ab B C h)

  right-distributive-comp-add-hom-Ab :
    (g h : hom-Ab B C) (f : hom-Ab A B) →
    comp-hom-Ab A B C (add-hom-Ab B C g h) f ＝
    add-hom-Ab A C (comp-hom-Ab A B C g f) (comp-hom-Ab A B C h f)
  right-distributive-comp-add-hom-Ab g h f =
    eq-htpy-hom-Ab A C (λ x → refl)
```

### Evaluation at an element is a group homomorphism `hom A B → A`

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2) (a : type-Ab A)
  where

  ev-element-hom-Ab : hom-Ab A B → type-Ab B
  ev-element-hom-Ab f = map-hom-Ab A B f a

  preserves-add-ev-element-hom-Ab :
    (f g : hom-Ab A B) →
    ev-element-hom-Ab (add-hom-Ab A B f g) ＝
    add-Ab B (ev-element-hom-Ab f) (ev-element-hom-Ab g)
  preserves-add-ev-element-hom-Ab f g = refl

  hom-ev-element-hom-Ab : hom-Ab (ab-hom-Ab A B) B
  pr1 hom-ev-element-hom-Ab = ev-element-hom-Ab
  pr2 hom-ev-element-hom-Ab {x} {y} = preserves-add-ev-element-hom-Ab x y
```
