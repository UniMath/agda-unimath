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
open import group-theory.subgroups
open import group-theory.symmetric-groups
open import group-theory.trivial-group-homomorphisms
```

</details>

## Idea

An **action** of a [group](group-theory.groups.md) `G` on a
[set](foundation-core.sets.md) `X`, also called a **`G`-action**, is a
[group homomorphism](group-theory.homomorphisms-groups.md) from `G` into
`symmetric-Group X`. A set equipped with a `G`-action is called a **`G`-set**.

## Definitions

### The type of `G`-sets

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

  equiv-mul-action-Group : type-Group G → type-action-Group ≃ type-action-Group
  equiv-mul-action-Group =
    map-hom-Group G (symmetric-Group set-action-Group) (pr2 X)

  mul-action-Group : type-Group G → type-action-Group → type-action-Group
  mul-action-Group g = map-equiv (equiv-mul-action-Group g)

  mul-action-Group' : type-action-Group → type-Group G → type-action-Group
  mul-action-Group' x g = mul-action-Group g x

  preserves-unit-mul-action-Group : mul-action-Group (unit-Group G) ~ id
  preserves-unit-mul-action-Group =
    htpy-eq
      ( ap pr1
        ( preserves-unit-hom-Group G
          ( symmetric-Group set-action-Group)
          ( pr2 X)))

  preserves-mul-action-Group :
    (g : type-Group G) (h : type-Group G) (x : type-action-Group) →
    mul-action-Group (mul-Group G g h) x ＝
    mul-action-Group g (mul-action-Group h x)
  preserves-mul-action-Group g h =
    htpy-eq
      ( ap pr1
        ( preserves-mul-hom-Group G (symmetric-Group set-action-Group) (pr2 X)))

  transpose-eq-mul-action-Group :
    (g : type-Group G) (x y : type-action-Group) →
    mul-action-Group g x ＝ y → x ＝ mul-action-Group (inv-Group G g) y
  transpose-eq-mul-action-Group g x ._ refl =
    ( inv
      ( ( ap (mul-action-Group' x) (left-inverse-law-mul-Group G g)) ∙
        ( preserves-unit-mul-action-Group x))) ∙
    ( preserves-mul-action-Group (inv-Group G g) g x)
```

## Examples

### Trivial `G`-sets

Every set gives rise to a `G`-set by having every point fixed under the action
of `G`.

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : Set l2)
  where

  trivial-action-Group : action-Group G l2
  pr1 trivial-action-Group = X
  pr2 trivial-action-Group = trivial-hom-Group G (symmetric-Group X)
```

## External links

- [Group action](https://en.wikipedia.org/wiki/Group_action) at Wikipedia
- [Actions of a group](https://ncatlab.org/nlab/show/action#ActionsOfAGroup) at
  $n$Lab
- [Group Action](https://mathworld.wolfram.com/GroupAction.html) at Wolfram
  MathWorld
