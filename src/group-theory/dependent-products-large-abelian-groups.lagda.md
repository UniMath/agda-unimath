# Dependent products of large abelian groups

```agda
module group-theory.dependent-products-large-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.dependent-products-large-groups
open import group-theory.large-abelian-groups
open import group-theory.large-groups
```

</details>

## Idea

The dependent product of a family of
[large abelian groups](group-theory.large-abelian-groups.md) is a large abelian
group.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {l0 : Level}
  (A : UU l0)
  (G : A → Large-Ab α β)
  where

  large-group-Π-Large-Ab : Large-Group (λ l → l0 ⊔ α l) (λ l1 l2 → l0 ⊔ β l1 l2)
  large-group-Π-Large-Ab =
    Π-Large-Group A (λ a → large-group-Large-Ab (G a))

  type-Π-Large-Ab : (l : Level) → UU (l0 ⊔ α l)
  type-Π-Large-Ab l = (a : A) → type-Large-Ab (G a) l

  add-Π-Large-Ab :
    {l1 l2 : Level} →
    type-Π-Large-Ab l1 → type-Π-Large-Ab l2 →
    type-Π-Large-Ab (l1 ⊔ l2)
  add-Π-Large-Ab f g a = add-Large-Ab (G a) (f a) (g a)

  abstract
    commutative-add-Π-Large-Ab :
      {l1 l2 : Level} (x : type-Π-Large-Ab l1) (y : type-Π-Large-Ab l2) →
      add-Π-Large-Ab x y ＝ add-Π-Large-Ab y x
    commutative-add-Π-Large-Ab x y =
      eq-htpy (λ a → commutative-add-Large-Ab (G a) (x a) (y a))

  Π-Large-Ab : Large-Ab (λ l → l0 ⊔ α l) (λ l1 l2 → l0 ⊔ β l1 l2)
  Π-Large-Ab =
    λ where
      .large-group-Large-Ab → large-group-Π-Large-Ab
      .commutative-add-Large-Ab → commutative-add-Π-Large-Ab
```
