# Group actions

```agda
module group-theory.group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.symmetric-groups
```

</details>

## Idea

A action of a group `G` on a set `X` is a group homomorphism from `G` into
`symmetric-Group X`.

## Definition

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  action-Group : (l : Level) → UU (l1 ⊔ lsuc l)
  action-Group l =
    Σ (Set l) (λ X → hom-Group G (symmetric-Group X))

module _
  {l1 l2 : Level} (G : Group l1) (X : action-Group G l2)
  where

  set-action-Group : Set l2
  set-action-Group = pr1 X

  type-action-Group : UU l2
  type-action-Group = type-Set set-action-Group

  is-set-type-action-Group : is-set type-action-Group
  is-set-type-action-Group = is-set-type-Set set-action-Group

  equiv-mul-action-Group :
    type-Group G → type-action-Group ≃ type-action-Group
  equiv-mul-action-Group =
    map-hom-Group G (symmetric-Group set-action-Group) (pr2 X)

  mul-action-Group :
    type-Group G → type-action-Group → type-action-Group
  mul-action-Group g =
    map-equiv (equiv-mul-action-Group g)

  mul-action-Group' :
    type-action-Group → type-Group G → type-action-Group
  mul-action-Group' x g = mul-action-Group g x

  preserves-unit-mul-action-Group :
    (mul-action-Group (unit-Group G)) ~ id
  preserves-unit-mul-action-Group =
    htpy-eq
      ( ap pr1
        ( preserves-unit-hom-Group G
          ( symmetric-Group set-action-Group)
          ( pr2 X)))

  preserves-mul-action-Group :
    (g : type-Group G) (h : type-Group G) (x : type-action-Group) →
    Id
      ( mul-action-Group (mul-Group G g h) x)
      ( mul-action-Group g (mul-action-Group h x))
  preserves-mul-action-Group g h =
    htpy-eq
      ( ap pr1
        ( preserves-mul-hom-Group G
          ( symmetric-Group set-action-Group) (pr2 X)))

  transpose-eq-mul-action-Group :
    (g : type-Group G) (x y : type-action-Group) →
    Id (mul-action-Group g x) y →
    Id x (mul-action-Group (inv-Group G g) y)
  transpose-eq-mul-action-Group g x ._ refl =
    ( inv
      ( ( ap (mul-action-Group' x) (left-inverse-law-mul-Group G g)) ∙
        ( preserves-unit-mul-action-Group x))) ∙
    ( preserves-mul-action-Group (inv-Group G g) g x)
```
