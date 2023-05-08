# Function class factorization operations

```agda
module orthogonal-factorization-systems.function-class-factorization-operations where
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

Given two function classes `L` and `R`, a **function class factorization
operation** is a factorization operation such that the left map of every
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

  function-class-factorization-operation :
    UU (l1 ⊔ l2 ⊔ lsuc lF ⊔ lL ⊔ lR)
  function-class-factorization-operation =
    (f : A → B) → function-class-factorization L R f

  mere-function-class-factorization-property :
    UU (l1 ⊔ l2 ⊔ lsuc lF ⊔ lL ⊔ lR)
  mere-function-class-factorization-property =
    (f : A → B) → is-inhabited (function-class-factorization L R f)

  unique-function-class-factorization-operation :
    UU (l1 ⊔ l2 ⊔ lsuc lF ⊔ lL ⊔ lR)
  unique-function-class-factorization-operation =
    (f : A → B) → is-contr (function-class-factorization L R f)
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

  mere-function-class-factorization-property-Prop :
    Prop (l1 ⊔ l2 ⊔ lsuc lF ⊔ lL ⊔ lR)
  mere-function-class-factorization-property-Prop =
    Π-Prop (A → B) (is-inhabited-Prop ∘ function-class-factorization L R)

  is-prop-mere-function-class-factorization-property :
    is-prop (mere-function-class-factorization-property L R A B)
  is-prop-mere-function-class-factorization-property =
    is-prop-type-Prop mere-function-class-factorization-property-Prop
```

### Having a unique function class factorization operation is a property

```agda
module _
  {l1 l2 lF lL lR : Level}
  (L : function-class l1 lF lL)
  (R : function-class lF l2 lR)
  {A : UU l1} {B : UU l2}
  where

  unique-function-class-factorization-operation-Prop :
    Prop (l1 ⊔ l2 ⊔ lsuc lF ⊔ lL ⊔ lR)
  unique-function-class-factorization-operation-Prop =
    Π-Prop (A → B) (is-contr-Prop ∘ function-class-factorization L R)

  is-prop-unique-function-class-factorization-operation :
    is-prop (unique-function-class-factorization-operation L R A B)
  is-prop-unique-function-class-factorization-operation =
    is-prop-type-Prop unique-function-class-factorization-operation-Prop
```
