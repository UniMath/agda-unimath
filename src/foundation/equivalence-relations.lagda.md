---
title: Equivalence relations
---

```agda
module foundation.equivalence-relations where

open import foundation-core.equivalence-relations public

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.partitions
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types

open import foundation-core.universe-levels
```

## Properties

### The type of equivalence relations on `A` is equivalent to the type of partitions on `A`

#### The partition obtained from an equivalence relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  subtype-inhabited-subtype-Eq-Rel : subtype (l1 ⊔ l2) (inhabited-subtype l2 A)
  subtype-inhabited-subtype-Eq-Rel Q =
    ∃-Prop A
      ( λ x →
        has-same-elements-subtype
          ( subtype-inhabited-subtype Q)
          ( prop-Eq-Rel R x))

  abstract
    is-partition-subtype-inhabited-subtype-Eq-Rel :
      is-partition subtype-inhabited-subtype-Eq-Rel
    pr1 (pr1 (pr1 (is-partition-subtype-inhabited-subtype-Eq-Rel x))) =
      prop-Eq-Rel R x
    pr2 (pr1 (pr1 (is-partition-subtype-inhabited-subtype-Eq-Rel x))) =
      unit-trunc-Prop (pair x (refl-Eq-Rel R))
    pr1 (pr2 (pr1 (is-partition-subtype-inhabited-subtype-Eq-Rel x))) =
      unit-trunc-Prop
        ( pair x (refl-has-same-elements-subtype (prop-Eq-Rel R x)))
    pr2 (pr2 (pr1 (is-partition-subtype-inhabited-subtype-Eq-Rel x))) =
      refl-Eq-Rel R
    pr2 (is-partition-subtype-inhabited-subtype-Eq-Rel x) Q =
      eq-type-subtype
        ( λ U →
          prod-Prop
            ( subtype-inhabited-subtype-Eq-Rel U)
            ( subtype-inhabited-subtype U x))
        ( eq-type-subtype
          ( λ U → trunc-Prop (type-subtype U))
          ( eq-has-same-elements-subtype
            ( prop-Eq-Rel R x)
            ( subtype-inhabited-subtype (pr1 Q))
            ( λ y →
              pair
                ( λ r →
                  apply-universal-property-trunc-Prop
                    ( pr1 (pr2 Q))
                    ( subtype-inhabited-subtype (pr1 Q) y)
                    ( λ { (z , H) →
                          pr2
                            ( H y)
                            ( trans-Eq-Rel R (pr1 (H x) (pr2 (pr2 Q))) r)}))
                ( λ q →
                  apply-universal-property-trunc-Prop
                    ( pr1 (pr2 Q))
                    ( prop-Eq-Rel R x y)
                    ( λ { (z , H) →
                          trans-Eq-Rel R
                            ( symm-Eq-Rel R (pr1 (H x) (pr2 (pr2 Q))))
                            ( pr1 (H y) q)})))))

  partition-Eq-Rel : partition l2 (l1 ⊔ l2) A
  pr1 partition-Eq-Rel = subtype-inhabited-subtype-Eq-Rel
  pr2 partition-Eq-Rel = is-partition-subtype-inhabited-subtype-Eq-Rel
```

#### The equivalence relation obtained from a partition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  where

  sim-partition : A → A → UU (l1 ⊔ lsuc l2 ⊔ l3)
  sim-partition x y =
    Σ ( block-partition P)
      ( λ Q → is-in-block-partition P Q x × is-in-block-partition P Q y)

  is-proof-irrelevant-sim-partition :
    (x y : A) → is-proof-irrelevant (sim-partition x y)
  is-proof-irrelevant-sim-partition x y (Q , p , q) =
    is-contr-equiv'
      ( Σ ( Σ (block-partition P) (λ Q → is-in-block-partition P Q x))
          ( λ Q → is-in-block-partition P (pr1 Q) y))
      ( assoc-Σ
        ( block-partition P)
        ( λ U → is-in-block-partition P U x)
        ( λ U → is-in-block-partition P (pr1 U) y))
      ( is-contr-Σ
        ( is-contr-equiv
          ( Σ ( inhabited-subtype l2 A)
              ( λ U →
                 type-Prop (subtype-partition P U) ×
                 is-in-inhabited-subtype U x))
          ( assoc-Σ
            ( inhabited-subtype l2 A)
            ( λ U → type-Prop (subtype-partition P U))
            ( λ U → is-in-inhabited-subtype (pr1 U) x))
          ( is-partition-subtype-partition P x))
        ( pair Q p)
        ( is-proof-irrelevant-is-prop
          ( is-prop-is-in-inhabited-subtype (pr1 Q) y)
          ( q)))

  is-prop-sim-partition : (x y : A) → is-prop (sim-partition x y)
  is-prop-sim-partition x y =
    is-prop-is-proof-irrelevant (is-proof-irrelevant-sim-partition x y)

  prop-eq-rel-partition : Rel-Prop (l1 ⊔ lsuc l2 ⊔ l3) A
  pr1 (prop-eq-rel-partition x y) = sim-partition x y
  pr2 (prop-eq-rel-partition x y) = is-prop-sim-partition x y

  refl-sim-partition : {x : A} → sim-partition x x
  pr1 (pr1 (refl-sim-partition {x})) =
    pr1 (center (is-partition-subtype-partition P x))
  pr2 (pr1 (refl-sim-partition {x})) =
    pr1 (pr2 (center (is-partition-subtype-partition P x)))
  pr1 (pr2 (refl-sim-partition {x})) =
    pr2 (pr2 (center (is-partition-subtype-partition P x)))
  pr2 (pr2 (refl-sim-partition {x})) =
    pr2 (pr2 (center (is-partition-subtype-partition P x)))

  symm-sim-partition : {x y : A} → sim-partition x y → sim-partition y x
  pr1 (symm-sim-partition {x} {y} (Q , p , q)) = Q
  pr1 (pr2 (symm-sim-partition {x} {y} (Q , p , q))) = q
  pr2 (pr2 (symm-sim-partition {x} {y} (Q , p , q))) = p

  trans-sim-partition :
    {x y z : A} → sim-partition x y → sim-partition y z → sim-partition x z
  pr1 (trans-sim-partition {x} {y} {z} (Q1 , p1 , q1) (Q2 , p2 , q2)) = Q1
  pr1 (pr2 (trans-sim-partition {x} {y} {z} (Q1 , p1 , q1) (Q2 , p2 , q2))) = p1
  pr2 (pr2 (trans-sim-partition {x} {y} {z} (Q1 , p1 , q1) (Q2 , p2 , q2))) =
    pr2
      ( has-same-elements-eq-subtype
        ( subtype-inhabited-subtype (pr1 Q1))
        ( subtype-inhabited-subtype (pr1 Q2))
        ( ap
          ( subtype-inhabited-subtype)
          ( ap
            ( pr1)
            ( eq-is-contr
              ( is-partition-subtype-partition P y)
              { pr1 Q1 , pr2 Q1 , q1}
              { pr1 Q2 , pr2 Q2 , p2})))
        ( z))
      ( q2)

  eq-rel-partition : Eq-Rel (l1 ⊔ lsuc l2 ⊔ l3) A
  pr1 eq-rel-partition = prop-eq-rel-partition
  pr1 (pr2 eq-rel-partition) = refl-sim-partition
  pr1 (pr2 (pr2 eq-rel-partition)) = symm-sim-partition
  pr2 (pr2 (pr2 eq-rel-partition)) = trans-sim-partition
```
