# Homomorphisms of abelian groups

```agda
module group-theory.homomorphisms-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.homomorphisms-commutative-monoids
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-semigroups
```

</details>

## Idea

Homomorphisms between abelian groups are just homomorphisms between their
underlying groups.

## Definition

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  preserves-add-Ab : (type-Ab A → type-Ab B) → UU (l1 ⊔ l2)
  preserves-add-Ab = preserves-mul-Semigroup (semigroup-Ab A) (semigroup-Ab B)

  hom-set-Ab : Set (l1 ⊔ l2)
  hom-set-Ab = hom-set-Group (group-Ab A) (group-Ab B)

  hom-Ab : UU (l1 ⊔ l2)
  hom-Ab = hom-Group (group-Ab A) (group-Ab B)

  map-hom-Ab : hom-Ab → type-Ab A → type-Ab B
  map-hom-Ab = map-hom-Group (group-Ab A) (group-Ab B)

  preserves-add-hom-Ab : (f : hom-Ab) → preserves-add-Ab (map-hom-Ab f)
  preserves-add-hom-Ab f = preserves-mul-hom-Group (group-Ab A) (group-Ab B) f

  preserves-zero-Ab : (type-Ab A → type-Ab B) → UU l2
  preserves-zero-Ab = preserves-unit-Group (group-Ab A) (group-Ab B)

  preserves-zero-hom-Ab : (f : hom-Ab) → preserves-zero-Ab (map-hom-Ab f)
  preserves-zero-hom-Ab f = preserves-unit-hom-Group (group-Ab A) (group-Ab B) f

  preserves-negatives-Ab : (type-Ab A → type-Ab B) → UU (l1 ⊔ l2)
  preserves-negatives-Ab f =
    (x : type-Ab A) → Id (f (neg-Ab A x)) (neg-Ab B (f x))

  preserves-negatives-hom-Ab :
    (f : hom-Ab) → preserves-negatives-Ab (map-hom-Ab f)
  preserves-negatives-hom-Ab f =
    preserves-inv-hom-Group (group-Ab A) (group-Ab B) f

  hom-semigroup-hom-Ab :
    hom-Ab → hom-Semigroup (semigroup-Ab A) (semigroup-Ab B)
  pr1 (hom-semigroup-hom-Ab f) = map-hom-Ab f
  pr2 (hom-semigroup-hom-Ab f) = preserves-add-hom-Ab f

  hom-commutative-monoid-hom-Ab :
    hom-Ab →
    hom-Commutative-Monoid
      ( commutative-monoid-Ab A)
      ( commutative-monoid-Ab B)
  pr1 (hom-commutative-monoid-hom-Ab f) = hom-semigroup-hom-Ab f
  pr2 (hom-commutative-monoid-hom-Ab f) = preserves-zero-hom-Ab f
```

### Characterization of the identity type of the abelian group homomorphisms

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  htpy-hom-Ab : (f g : hom-Ab A B) → UU (l1 ⊔ l2)
  htpy-hom-Ab f g = htpy-hom-Group (group-Ab A) (group-Ab B) f g

  refl-htpy-hom-Ab : (f : hom-Ab A B) → htpy-hom-Ab f f
  refl-htpy-hom-Ab f = refl-htpy-hom-Group (group-Ab A) (group-Ab B) f

  htpy-eq-hom-Ab : (f g : hom-Ab A B) → Id f g → htpy-hom-Ab f g
  htpy-eq-hom-Ab f g = htpy-eq-hom-Group (group-Ab A) (group-Ab B) f g

  abstract
    is-contr-total-htpy-hom-Ab :
      (f : hom-Ab A B) → is-contr (Σ (hom-Ab A B) (htpy-hom-Ab f))
    is-contr-total-htpy-hom-Ab f =
      is-contr-total-htpy-hom-Group (group-Ab A) (group-Ab B) f

  abstract
    is-equiv-htpy-eq-hom-Ab :
      (f g : hom-Ab A B) → is-equiv (htpy-eq-hom-Ab f g)
    is-equiv-htpy-eq-hom-Ab f g =
      is-equiv-htpy-eq-hom-Group (group-Ab A) (group-Ab B) f g

  eq-htpy-hom-Ab : {f g : hom-Ab A B} → htpy-hom-Ab f g → Id f g
  eq-htpy-hom-Ab = eq-htpy-hom-Group (group-Ab A) (group-Ab B)

  is-set-hom-Ab : is-set (hom-Ab A B)
  is-set-hom-Ab = is-set-hom-Group (group-Ab A) (group-Ab B)
```

### The identity morphism of abelian groups

```agda
preserves-add-id : {l : Level} (A : Ab l) → preserves-add-Ab A A id
preserves-add-id A = preserves-mul-id-Semigroup (semigroup-Ab A)

id-hom-Ab : {l1 : Level} (A : Ab l1) → hom-Ab A A
id-hom-Ab A = id-hom-Group (group-Ab A)
```

### Composition of morphisms of abelian groups

```agda
comp-hom-Ab :
  { l1 l2 l3 : Level} (A : Ab l1) (B : Ab l2) (C : Ab l3) →
  ( hom-Ab B C) → (hom-Ab A B) → (hom-Ab A C)
comp-hom-Ab A B C =
  comp-hom-Group (group-Ab A) (group-Ab B) (group-Ab C)
```

### Associativity of composition of morphisms of abelian groups

```agda
associative-comp-hom-Ab :
  { l1 l2 l3 l4 : Level} (A : Ab l1) (B : Ab l2) (C : Ab l3) (D : Ab l4) →
  ( h : hom-Ab C D) (g : hom-Ab B C) (f : hom-Ab A B) →
  Id
    ( comp-hom-Ab A B D (comp-hom-Ab B C D h g) f)
    ( comp-hom-Ab A C D h (comp-hom-Ab A B C g f))
associative-comp-hom-Ab A B C D =
  associative-comp-hom-Semigroup
    ( semigroup-Ab A)
    ( semigroup-Ab B)
    ( semigroup-Ab C)
    ( semigroup-Ab D)
```

### The unit laws for composition of abelian groups

```agda
left-unit-law-comp-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  ( f : hom-Ab A B) → Id (comp-hom-Ab A B B (id-hom-Ab B) f) f
left-unit-law-comp-hom-Ab A B =
  left-unit-law-comp-hom-Semigroup (semigroup-Ab A) (semigroup-Ab B)

right-unit-law-comp-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  ( f : hom-Ab A B) → Id (comp-hom-Ab A A B f (id-hom-Ab A)) f
right-unit-law-comp-hom-Ab A B =
  right-unit-law-comp-hom-Semigroup (semigroup-Ab A) (semigroup-Ab B)
```
