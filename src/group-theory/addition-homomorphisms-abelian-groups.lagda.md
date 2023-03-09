# Pointwise addition of morphisms of abelian groups

```agda
module group-theory.addition-homomorphisms-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups
```

</details>

## Idea

Morphisms of abelian groups can be added pointwise. This operation turns each hom-set of abelian groups into an abelian group. Moreover, composition of abelian groups distributes over addition from the left and from the right.

## Definition

### Pointwise operations on morphisms between abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  add-hom-Ab :
    type-hom-Ab A B → type-hom-Ab A B → type-hom-Ab A B
  pr1 (add-hom-Ab f g) x = add-Ab B (map-hom-Ab A B f x) (map-hom-Ab A B g x)
  pr2 (add-hom-Ab f g) x y =
    ( ap-add-Ab B
      ( preserves-add-hom-Ab A B f x y)
      ( preserves-add-hom-Ab A B g x y)) ∙
    ( interchange-add-add-Ab B
      ( map-hom-Ab A B f x)
      ( map-hom-Ab A B f y)
      ( map-hom-Ab A B g x)
      ( map-hom-Ab A B g y))

  zero-hom-Ab : type-hom-Ab A B
  pr1 zero-hom-Ab x = zero-Ab B
  pr2 zero-hom-Ab x y = inv (left-unit-law-add-Ab B (zero-Ab B))

  neg-hom-Ab : type-hom-Ab A B → type-hom-Ab A B
  pr1 (neg-hom-Ab f) x = neg-Ab B (map-hom-Ab A B f x)
  pr2 (neg-hom-Ab f) x y =
    ( ap (neg-Ab B) (preserves-add-hom-Ab A B f x y)) ∙
    ( distributive-neg-add-Ab B (map-hom-Ab A B f x) (map-hom-Ab A B f y))
```

### Associativity of pointwise addition of morphisms of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  associative-add-hom-Ab :
    (f g h : type-hom-Ab A B) →
    Id ( add-hom-Ab A B (add-hom-Ab A B f g) h)
       ( add-hom-Ab A B f (add-hom-Ab A B g h))
  associative-add-hom-Ab f g h =
    eq-htpy-hom-Ab A B
      ( λ x →
        associative-add-Ab B
          ( map-hom-Ab A B f x)
          ( map-hom-Ab A B g x)
          ( map-hom-Ab A B h x))
```

### Commutativity of pointwise addition of morphisms of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  commutative-add-hom-Ab :
    (f g : type-hom-Ab A B) → Id (add-hom-Ab A B f g) (add-hom-Ab A B g f)
  commutative-add-hom-Ab f g =
    eq-htpy-hom-Ab A B
      ( λ x → commutative-add-Ab B (map-hom-Ab A B f x) (map-hom-Ab A B g x))
```

### Unit laws for pointwise addition of morphisms of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  left-unit-law-add-hom-Ab :
    (f : type-hom-Ab A B) → Id (add-hom-Ab A B (zero-hom-Ab A B) f) f
  left-unit-law-add-hom-Ab f =
    eq-htpy-hom-Ab A B (λ x → left-unit-law-add-Ab B (map-hom-Ab A B f x))

  right-unit-law-add-hom-Ab :
    (f : type-hom-Ab A B) → Id (add-hom-Ab A B f (zero-hom-Ab A B)) f
  right-unit-law-add-hom-Ab f =
    eq-htpy-hom-Ab A B (λ x → right-unit-law-add-Ab B (map-hom-Ab A B f x))
```

### Inverse laws for pointwise addition of morphisms of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  left-inverse-law-add-hom-Ab :
    (f : type-hom-Ab A B) →
    Id (add-hom-Ab A B (neg-hom-Ab A B f) f) (zero-hom-Ab A B)
  left-inverse-law-add-hom-Ab f =
    eq-htpy-hom-Ab A B (λ x → left-inverse-law-add-Ab B (map-hom-Ab A B f x))

  right-inverse-law-add-hom-Ab :
    (f : type-hom-Ab A B) →
    Id (add-hom-Ab A B f (neg-hom-Ab A B f)) (zero-hom-Ab A B)
  right-inverse-law-add-hom-Ab f =
    eq-htpy-hom-Ab A B (λ x → right-inverse-law-add-Ab B (map-hom-Ab A B f x))
```

### Distributivity of composition over pointwise addition of morphisms of abelian groups

```agda
module _
  {l1 l2 l3 : Level} (A : Ab l1) (B : Ab l2) (C : Ab l3)
  where

  left-distributive-comp-add-hom-Ab :
    (h : type-hom-Ab B C) (f g : type-hom-Ab A B) →
    Id ( comp-hom-Ab A B C h (add-hom-Ab A B f g))
       ( add-hom-Ab A C (comp-hom-Ab A B C h f) (comp-hom-Ab A B C h g))
  left-distributive-comp-add-hom-Ab h f g =
    eq-htpy-hom-Ab A C
      ( λ x →
        preserves-add-hom-Ab B C h (map-hom-Ab A B f x) (map-hom-Ab A B g x))

  right-distributive-comp-add-hom-Ab :
    (g h : type-hom-Ab B C) (f : type-hom-Ab A B) →
    Id ( comp-hom-Ab A B C (add-hom-Ab B C g h) f)
       ( add-hom-Ab A C (comp-hom-Ab A B C g f) (comp-hom-Ab A B C h f))
  right-distributive-comp-add-hom-Ab g h f =
    eq-htpy-hom-Ab A C (λ x → refl)
```
