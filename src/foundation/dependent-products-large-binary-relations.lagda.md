# Dependent products of large binary relations

```agda
module foundation.dependent-products-large-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

[Large binary relations](foundation.large-binary-relations.md) can be extended
to dependent products.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {l0 : Level}
  (I : UU l0)
  (X : I → (l : Level) → UU (α l))
  where

  Π-Large-Relation :
    ((i : I) → Large-Relation β (X i)) →
    Large-Relation (λ l1 l2 → l0 ⊔ β l1 l2) (λ l → (i : I) → X i l)
  Π-Large-Relation R f g = (i : I) → R i (f i) (g i)

  Π-Large-Relation-Prop :
    ((i : I) → Large-Relation-Prop β (X i)) →
    Large-Relation-Prop (λ l1 l2 → l0 ⊔ β l1 l2) (λ l → (i : I) → X i l)
  Π-Large-Relation-Prop R f g =
    Π-Prop I (λ i → R i (f i) (g i))
```

## Properties

### Reflexivity of dependent products of large binary relations

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {l0 : Level}
  (I : UU l0)
  (X : I → (l : Level) → UU (α l))
  (R : (i : I) → Large-Relation β (X i))
  where

  is-reflexive-Π-Large-Relation :
    ((i : I) → is-reflexive-Large-Relation (X i) (R i)) →
    is-reflexive-Large-Relation (λ l → (i : I) → X i l) (Π-Large-Relation I X R)
  is-reflexive-Π-Large-Relation refl-R f i = refl-R i (f i)
```

### Symmetry of dependent products of large binary relations

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {l0 : Level}
  (I : UU l0)
  (X : I → (l : Level) → UU (α l))
  (R : (i : I) → Large-Relation β (X i))
  where

  is-symmetric-Π-Large-Relation :
    ((i : I) → is-symmetric-Large-Relation (X i) (R i)) →
    is-symmetric-Large-Relation (λ l → (i : I) → X i l) (Π-Large-Relation I X R)
  is-symmetric-Π-Large-Relation sym-R f g f~g i = sym-R i (f i) (g i) (f~g i)
```

### Transitivity of dependent products of large binary relations

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {l0 : Level}
  (I : UU l0)
  (X : I → (l : Level) → UU (α l))
  (R : (i : I) → Large-Relation β (X i))
  where

  is-transitive-Π-Large-Relation :
    ((i : I) → is-transitive-Large-Relation (X i) (R i)) →
    is-transitive-Large-Relation
      ( λ l → (i : I) → X i l)
      ( Π-Large-Relation I X R)
  is-transitive-Π-Large-Relation trans-R f g h g~h f~g i =
    trans-R i (f i) (g i) (h i) (g~h i) (f~g i)
```
