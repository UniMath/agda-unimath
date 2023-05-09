# Factorization operations into function classes

```agda
module orthogonal-factorization-systems.factorization-operations-function-classes where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.functions
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.universe-levels

open import orthogonal-factorization-systems.factorizations-of-maps
open import orthogonal-factorization-systems.function-classes
```

</details>

## Idea

A **factorization operation into function classes** is a factorization operation
equipped with two function classes `L` and `R` such that the left map of every
factorization is in `L`, and the right map is in `R`.

```md
       ∙
      ^ \
 L ∋ /   \ ∈ R
    /     v
  A -----> B
```

## Definition

```agda
module _
  {l1 l2 lF lL lR : Level}
  (L : function-class l1 lF lL)
  (R : function-class lF l2 lR)
  (A : UU l1) (B : UU l2)
  where

  factorization-operation-function-class :
    UU (l1 ⊔ l2 ⊔ lsuc lF ⊔ lL ⊔ lR)
  factorization-operation-function-class =
    (f : A → B) → factorization-function-class L R f

  mere-factorization-property-function-class :
    UU (l1 ⊔ l2 ⊔ lsuc lF ⊔ lL ⊔ lR)
  mere-factorization-property-function-class =
    (f : A → B) → is-inhabited (factorization-function-class L R f)

  unique-factorization-operation-function-class :
    UU (l1 ⊔ l2 ⊔ lsuc lF ⊔ lL ⊔ lR)
  unique-factorization-operation-function-class =
    (f : A → B) → is-contr (factorization-function-class L R f)
```

## Properties

### A mere function class factorization property is a property

```agda
module _
  {l1 l2 lF lL lR : Level}
  (L : function-class l1 lF lL)
  (R : function-class lF l2 lR)
  {A : UU l1} {B : UU l2}
  where

  mere-factorization-property-function-class-Prop :
    Prop (l1 ⊔ l2 ⊔ lsuc lF ⊔ lL ⊔ lR)
  mere-factorization-property-function-class-Prop =
    Π-Prop (A → B) (is-inhabited-Prop ∘ factorization-function-class L R)

  is-prop-mere-factorization-property-function-class :
    is-prop (mere-factorization-property-function-class L R A B)
  is-prop-mere-factorization-property-function-class =
    is-prop-type-Prop mere-factorization-property-function-class-Prop
```

### Having a unique function class factorization operation is a property

```agda
module _
  {l1 l2 lF lL lR : Level}
  (L : function-class l1 lF lL)
  (R : function-class lF l2 lR)
  {A : UU l1} {B : UU l2}
  where

  unique-factorization-operation-function-class-Prop :
    Prop (l1 ⊔ l2 ⊔ lsuc lF ⊔ lL ⊔ lR)
  unique-factorization-operation-function-class-Prop =
    Π-Prop (A → B) (is-contr-Prop ∘ factorization-function-class L R)

  is-prop-unique-factorization-operation-function-class :
    is-prop (unique-factorization-operation-function-class L R A B)
  is-prop-unique-factorization-operation-function-class =
    is-prop-type-Prop unique-factorization-operation-function-class-Prop
```
