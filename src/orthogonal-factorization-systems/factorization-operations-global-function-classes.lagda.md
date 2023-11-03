# Factorization operations into global function classes

```agda
module orthogonal-factorization-systems.factorization-operations-global-function-classes where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import orthogonal-factorization-systems.factorization-operations-function-classes
open import orthogonal-factorization-systems.factorizations-of-maps-global-function-classes
open import orthogonal-factorization-systems.global-function-classes
```

</details>

## Idea

A **factorization operation into global function classes** `L` and `R` is a
[factorization operation](orthogonal-factorization-systems.factorization-operations.md)
such that the left map (in diagrammatic order) of every
[factorization](orthogonal-factorization-systems.factorizations-of-maps.md) is
in `L`, and the right map is in `R`.

```text
      Im f
      ^  \
 L ∋ /    \ ∈ R
    /      v
  A ------> B
       f
```

## Definitions

### Factorization operations into global function classes

```agda
module _
  {βL βR : Level → Level → Level}
  (L : global-function-class βL)
  (R : global-function-class βR)
  where

  factorization-operation-global-function-class-Level :
    (l1 l2 l3 : Level) → UU (βL l1 l3 ⊔ βR l3 l2 ⊔ lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  factorization-operation-global-function-class-Level l1 l2 l3 =
    {A : UU l1} {B : UU l2} (f : A → B) →
    global-function-class-factorization L R l3 f

  factorization-operation-global-function-class : UUω
  factorization-operation-global-function-class =
    {l1 l2 l3 : Level} →
    factorization-operation-global-function-class-Level l1 l2 l3
```

### Unique factorization operations into global function classes

```agda
module _
  {βL βR : Level → Level → Level}
  (L : global-function-class βL)
  (R : global-function-class βR)
  where

  unique-factorization-operation-global-function-class-Level :
    (l1 l2 l3 : Level) → UU (βL l1 l3 ⊔ βR l3 l2 ⊔ lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  unique-factorization-operation-global-function-class-Level l1 l2 l3 =
    unique-factorization-operation-function-class
      ( function-class-global-function-class L {l1} {l3})
      ( function-class-global-function-class R {l3} {l2})

  is-prop-unique-factorization-operation-global-function-class-Level :
    {l1 l2 l3 : Level} →
    is-prop
      ( unique-factorization-operation-global-function-class-Level l1 l2 l3)
  is-prop-unique-factorization-operation-global-function-class-Level =
    is-prop-unique-factorization-operation-function-class
      ( function-class-global-function-class L)
      ( function-class-global-function-class R)

  unique-factorization-operation-global-function-class-Level-Prop :
    (l1 l2 l3 : Level) →
    Prop (βL l1 l3 ⊔ βR l3 l2 ⊔ lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  unique-factorization-operation-global-function-class-Level-Prop l1 l2 l3 =
    unique-factorization-operation-function-class-Prop
      ( function-class-global-function-class L {l1} {l3})
      ( function-class-global-function-class R {l3} {l2})

  unique-factorization-operation-global-function-class : UUω
  unique-factorization-operation-global-function-class =
    {l1 l2 l3 : Level} →
    unique-factorization-operation-global-function-class-Level l1 l2 l3
```

### Mere factorization properties into global function classes

```agda
module _
  {βL βR : Level → Level → Level}
  (L : global-function-class βL)
  (R : global-function-class βR)
  where

  mere-factorization-property-global-function-class-Level :
    (l1 l2 l3 : Level) → UU (βL l1 l3 ⊔ βR l3 l2 ⊔ lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  mere-factorization-property-global-function-class-Level l1 l2 l3 =
    mere-factorization-property-function-class
      ( function-class-global-function-class L {l1} {l3})
      ( function-class-global-function-class R {l3} {l2})

  is-prop-mere-factorization-property-global-function-class-Level :
    {l1 l2 l3 : Level} →
    is-prop (mere-factorization-property-global-function-class-Level l1 l2 l3)
  is-prop-mere-factorization-property-global-function-class-Level =
    is-prop-mere-factorization-property-function-class
      ( function-class-global-function-class L)
      ( function-class-global-function-class R)

  mere-factorization-property-global-function-class-Prop :
    (l1 l2 l3 : Level) →
    Prop (βL l1 l3 ⊔ βR l3 l2 ⊔ lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  mere-factorization-property-global-function-class-Prop l1 l2 l3 =
    mere-factorization-property-function-class-Prop
      ( function-class-global-function-class L {l1} {l3})
      ( function-class-global-function-class R {l3} {l2})

  mere-factorization-property-global-function-class : UUω
  mere-factorization-property-global-function-class =
    {l1 l2 l3 : Level} →
    mere-factorization-property-global-function-class-Level l1 l2 l3
```
