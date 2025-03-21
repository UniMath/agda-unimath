# Discrete categories

```agda
module category-theory.discrete-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels
```

</details>

### Discrete precategories

Any set induces a discrete category whose objects are elements of the set and
which contains no-nonidentity morphisms.

```agda
module _
  {l : Level} (X : Set l)
  where

  discrete-precategory-Set : Precategory l l
  discrete-precategory-Set =
    make-Precategory
      ( type-Set X)
      ( λ x y → set-Prop (Id-Prop X x y))
      ( λ p q → q ∙ p)
      ( λ x → refl)
      ( λ h g f → inv (assoc f g h))
      ( λ _ → right-unit)
      ( λ _ → left-unit)
```
