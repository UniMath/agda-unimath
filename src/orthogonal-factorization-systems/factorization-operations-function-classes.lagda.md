# Factorization operations into function classes

```agda
module orthogonal-factorization-systems.factorization-operations-function-classes where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import orthogonal-factorization-systems.factorizations-of-maps
open import orthogonal-factorization-systems.factorizations-of-maps-function-classes
open import orthogonal-factorization-systems.function-classes
open import orthogonal-factorization-systems.lifting-squares
```

</details>

## Idea

A **factorization operation into (small) function classes** `L` and `R` is a
[factorization operation](orthogonal-factorization-systems.factorization-operations.md)
such that the left map (in diagrammatic order) of every
[factorization](orthogonal-factorization-systems.factorizations-of-maps.md) is
in `L`, and the right map is in `R`.

```text
       ∙
      ^ \
 L ∋ /   \ ∈ R
    /     v
  A -----> B
```

## Definitions

### Factorization operations into function classes

```agda
module _
  {l1 l2 l3 lL lR : Level}
  (L : function-class l1 l3 lL)
  (R : function-class l3 l2 lR)
  where

  instance-factorization-operation-function-class :
    (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lL ⊔ lR)
  instance-factorization-operation-function-class A B =
    (f : A → B) → function-class-factorization L R f

  factorization-operation-function-class :
    UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lL ⊔ lR)
  factorization-operation-function-class =
    {A : UU l1} {B : UU l2} →
    instance-factorization-operation-function-class A B
```

### Unique factorization operations into function classes

```agda
module _
  {l1 l2 l3 lL lR : Level}
  (L : function-class l1 l3 lL)
  (R : function-class l3 l2 lR)
  where

  instance-unique-factorization-operation-function-class :
    (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lL ⊔ lR)
  instance-unique-factorization-operation-function-class A B =
    (f : A → B) → is-contr (function-class-factorization L R f)

  unique-factorization-operation-function-class :
    UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lL ⊔ lR)
  unique-factorization-operation-function-class =
    {A : UU l1} {B : UU l2} →
    instance-unique-factorization-operation-function-class A B

  is-prop-unique-factorization-operation-function-class :
    is-prop unique-factorization-operation-function-class
  is-prop-unique-factorization-operation-function-class =
    is-prop-iterated-implicit-Π 2
      ( λ A B → is-prop-Π (λ f → is-property-is-contr))

  unique-factorization-operation-function-class-Prop :
    Prop (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lL ⊔ lR)
  pr1 unique-factorization-operation-function-class-Prop =
    unique-factorization-operation-function-class
  pr2 unique-factorization-operation-function-class-Prop =
    is-prop-unique-factorization-operation-function-class

  factorization-operation-unique-factorization-operation-function-class :
    unique-factorization-operation-function-class →
    factorization-operation-function-class L R
  factorization-operation-unique-factorization-operation-function-class F f =
    center (F f)
```

### Mere factorization properties into function classes

```agda
module _
  {l1 l2 l3 lL lR : Level}
  (L : function-class l1 l3 lL)
  (R : function-class l3 l2 lR)
  where

  instance-mere-factorization-property-function-class :
    (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lL ⊔ lR)
  instance-mere-factorization-property-function-class A B =
    (f : A → B) → is-inhabited (function-class-factorization L R f)

  mere-factorization-property-function-class :
    UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lL ⊔ lR)
  mere-factorization-property-function-class =
    {A : UU l1} {B : UU l2} →
    instance-mere-factorization-property-function-class A B

  is-prop-mere-factorization-property-function-class :
    is-prop mere-factorization-property-function-class
  is-prop-mere-factorization-property-function-class =
    is-prop-iterated-implicit-Π 2
      ( λ A B →
        is-prop-Π
          ( λ f →
            is-property-is-inhabited (function-class-factorization L R f)))

  mere-factorization-property-function-class-Prop :
    Prop (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lL ⊔ lR)
  pr1 mere-factorization-property-function-class-Prop =
    mere-factorization-property-function-class
  pr2 mere-factorization-property-function-class-Prop =
    is-prop-mere-factorization-property-function-class
```

## References

- Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
  theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
  ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
  [DOI:10.23638/LMCS-16(1:2)2020](https://doi.org/10.23638/LMCS-16%281%3A2%292020))

## See also

- [Factorization operations into global function classes](orthogonal-factorization-systems.factorization-operations-global-function-classes.md)
  for the universe polymorphic version.
