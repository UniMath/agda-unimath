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
open import foundation.equational-reasoning
open import foundation.equivalence-classes
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.partitions
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types

open import foundation-core.universe-levels
```

## Properties

### Characterization of equality in the type of equivalence relations

```agda
relates-same-elements-Eq-Rel :
  {l1 l2 l3 : Level} {A : UU l1} → Eq-Rel l2 A → Eq-Rel l3 A → UU (l1 ⊔ l2 ⊔ l3)
relates-same-elements-Eq-Rel R S =
  relates-same-elements-Rel-Prop (prop-Eq-Rel R) (prop-Eq-Rel S)

module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  refl-relates-same-elements-Eq-Rel : relates-same-elements-Eq-Rel R R
  refl-relates-same-elements-Eq-Rel =
    refl-relates-same-elements-Rel-Prop (prop-Eq-Rel R)

  is-contr-total-relates-same-elements-Eq-Rel :
    is-contr (Σ (Eq-Rel l2 A) (relates-same-elements-Eq-Rel R))
  is-contr-total-relates-same-elements-Eq-Rel =
    is-contr-total-Eq-subtype
      ( is-contr-total-relates-same-elements-Rel-Prop (prop-Eq-Rel R))
      ( is-prop-is-equivalence-relation)
      ( prop-Eq-Rel R)
      ( refl-relates-same-elements-Eq-Rel)
      ( is-equivalence-relation-prop-Eq-Rel R)

  relates-same-elements-eq-Eq-Rel :
    (S : Eq-Rel l2 A) → (R ＝ S) → relates-same-elements-Eq-Rel R S
  relates-same-elements-eq-Eq-Rel .R refl = refl-relates-same-elements-Eq-Rel

  is-equiv-relates-same-elements-eq-Eq-Rel :
    (S : Eq-Rel l2 A) → is-equiv (relates-same-elements-eq-Eq-Rel S)
  is-equiv-relates-same-elements-eq-Eq-Rel =
    fundamental-theorem-id
      is-contr-total-relates-same-elements-Eq-Rel
      relates-same-elements-eq-Eq-Rel

  extensionality-Eq-Rel :
    (S : Eq-Rel l2 A) → (R ＝ S) ≃ relates-same-elements-Eq-Rel R S
  pr1 (extensionality-Eq-Rel S) = relates-same-elements-eq-Eq-Rel S
  pr2 (extensionality-Eq-Rel S) = is-equiv-relates-same-elements-eq-Eq-Rel S

  eq-relates-same-elements-Eq-Rel :
    (S : Eq-Rel l2 A) → relates-same-elements-Eq-Rel R S → (R ＝ S)
  eq-relates-same-elements-Eq-Rel S =
    map-inv-equiv (extensionality-Eq-Rel S)
```

### The type of equivalence relations on `A` is equivalent to the type of partitions on `A`

#### The partition obtained from an equivalence relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  is-partition-is-equivalence-class-inhabited-subtype-Eq-Rel :
    is-partition (is-equivalence-class-inhabited-subtype-Eq-Rel R)
  is-partition-is-equivalence-class-inhabited-subtype-Eq-Rel x =
    is-contr-equiv
      ( Σ ( Σ ( equivalence-class R)
              ( λ C → is-in-equivalence-class R C x))
          ( λ t → is-inhabited-subtype (subtype-equivalence-class R (pr1 t))))
      ( ( equiv-Σ
          ( λ t → is-inhabited-subtype (subtype-equivalence-class R (pr1 t)))
          ( inv-assoc-Σ
            ( subtype l2 A)
            ( is-equivalence-class R)
            ( λ C → is-in-equivalence-class R C x))
          ( λ t → id-equiv)) ∘e
        ( equiv-right-swap-Σ))
      ( is-contr-Σ
        ( is-contr-total-is-in-equivalence-class R x)
        ( center-total-is-in-equivalence-class R x)
        ( is-proof-irrelevant-is-prop
          ( is-prop-type-trunc-Prop)
          ( is-inhabited-subtype-equivalence-class R (class R x))))

  partition-Eq-Rel : partition l2 (l1 ⊔ l2) A
  pr1 partition-Eq-Rel = is-equivalence-class-inhabited-subtype-Eq-Rel R
  pr2 partition-Eq-Rel =
    is-partition-is-equivalence-class-inhabited-subtype-Eq-Rel
```

#### The equivalence relation obtained from a partition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  where

  sim-partition' : A → A → UU (l1 ⊔ lsuc l2 ⊔ l3)
  sim-partition' x y =
    Σ ( large-block-partition P)
      ( λ Q →
        is-in-large-block-partition P Q x ×
        is-in-large-block-partition P Q y)

  sim-partition : A → A → UU (l1 ⊔ l2)
  sim-partition x y =
    Σ ( block-partition P)
      ( λ Q → is-in-block-partition P Q x × is-in-block-partition P Q y)

  compute-sim-partition : (x y : A) → sim-partition' x y ≃ sim-partition x y
  compute-sim-partition x y =
    equiv-Σ
      ( λ Q → is-in-block-partition P Q x × is-in-block-partition P Q y)
      ( compute-block-partition P)
      ( λ Q →
        equiv-prod
          ( compute-is-in-block-partition P Q x)
          ( compute-is-in-block-partition P Q y))

  is-proof-irrelevant-sim-partition' :
    (x y : A) → is-proof-irrelevant (sim-partition' x y)
  is-proof-irrelevant-sim-partition' x y (Q , p , q) =
    is-contr-equiv'
      ( Σ ( Σ ( large-block-partition P)
              ( λ B → is-in-large-block-partition P B x))
          ( λ B → is-in-large-block-partition P (pr1 B) y))
      ( assoc-Σ
        ( large-block-partition P)
        ( λ U → is-in-large-block-partition P U x)
        ( λ U → is-in-large-block-partition P (pr1 U) y))
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
          ( is-prop-is-in-inhabited-subtype
            ( pr1 Q)
            y)
          ( q)))

  is-prop-sim-partition' : (x y : A) → is-prop (sim-partition' x y)
  is-prop-sim-partition' x y =
    is-prop-is-proof-irrelevant (is-proof-irrelevant-sim-partition' x y)
    
  is-prop-sim-partition : (x y : A) → is-prop (sim-partition x y)
  is-prop-sim-partition x y =
    is-prop-equiv' (compute-sim-partition x y) (is-prop-sim-partition' x y)

  prop-eq-rel-partition' : Rel-Prop (l1 ⊔ lsuc l2 ⊔ l3) A
  pr1 (prop-eq-rel-partition' x y) = sim-partition' x y
  pr2 (prop-eq-rel-partition' x y) = is-prop-sim-partition' x y

  prop-eq-rel-partition : Rel-Prop (l1 ⊔ l2) A
  pr1 (prop-eq-rel-partition x y) = sim-partition x y
  pr2 (prop-eq-rel-partition x y) = is-prop-sim-partition x y

  refl-sim-partition' : {x : A} → sim-partition' x x
  pr1 (pr1 (refl-sim-partition' {x})) =
    pr1 (center (is-partition-subtype-partition P x))
  pr2 (pr1 (refl-sim-partition' {x})) =
    pr1 (pr2 (center (is-partition-subtype-partition P x)))
  pr1 (pr2 (refl-sim-partition' {x})) =
    pr2 (pr2 (center (is-partition-subtype-partition P x)))
  pr2 (pr2 (refl-sim-partition' {x})) =
    pr2 (pr2 (center (is-partition-subtype-partition P x)))

  refl-sim-partition : {x : A} → sim-partition x x
  refl-sim-partition {x} =
    map-equiv (compute-sim-partition x x) refl-sim-partition'

  symm-sim-partition' : {x y : A} → sim-partition' x y → sim-partition' y x
  pr1 (symm-sim-partition' {x} {y} (Q , p , q)) = Q
  pr1 (pr2 (symm-sim-partition' {x} {y} (Q , p , q))) = q
  pr2 (pr2 (symm-sim-partition' {x} {y} (Q , p , q))) = p

  symm-sim-partition : {x y : A} → sim-partition x y → sim-partition y x
  pr1 (symm-sim-partition {x} {y} (Q , p , q)) = Q
  pr1 (pr2 (symm-sim-partition {x} {y} (Q , p , q))) = q
  pr2 (pr2 (symm-sim-partition {x} {y} (Q , p , q))) = p

  trans-sim-partition' :
    {x y z : A} → sim-partition' x y → sim-partition' y z → sim-partition' x z
  pr1 (trans-sim-partition' {x} {y} {z} (Q1 , p1 , q1) (Q2 , p2 , q2)) = Q1
  pr1
    ( pr2
      ( trans-sim-partition' ((Q , u) , p , q) ((Q' , u') , p' , q'))) = p
  pr2 (pr2 (trans-sim-partition' ((Q , u) , p , q) ((Q' , u') , p' , q'))) =
    backward-implication
      ( has-same-elements-eq-inhabited-subtype Q Q'
        ( ap
          ( pr1)
          ( eq-is-contr
            ( is-partition-subtype-partition P _)
            { Q , u , q}
            { Q' , u' , p'}))
        ( _))
      ( q')

  trans-sim-partition :
    {x y z : A} → sim-partition x y → sim-partition y z → sim-partition x z
  trans-sim-partition {x} {y} {z} H K =
    map-equiv
      ( compute-sim-partition x z)
      ( trans-sim-partition'
        ( map-inv-equiv (compute-sim-partition x y) H)
        ( map-inv-equiv (compute-sim-partition y z) K))

  eq-rel-partition' : Eq-Rel (l1 ⊔ lsuc l2 ⊔ l3) A
  pr1 eq-rel-partition' = prop-eq-rel-partition'
  pr1 (pr2 eq-rel-partition') = refl-sim-partition'
  pr1 (pr2 (pr2 eq-rel-partition')) = symm-sim-partition'
  pr2 (pr2 (pr2 eq-rel-partition')) = trans-sim-partition'

  eq-rel-partition : Eq-Rel (l1 ⊔ l2) A
  pr1 eq-rel-partition = prop-eq-rel-partition
  pr1 (pr2 eq-rel-partition) = refl-sim-partition
  pr1 (pr2 (pr2 eq-rel-partition)) = symm-sim-partition
  pr2 (pr2 (pr2 eq-rel-partition)) = trans-sim-partition
```

### The equivalence relation obtained from the partition induced by an equivalence relation `R` is `R` itself

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  relates-same-elements-eq-rel-partition-Eq-Rel' :
    relates-same-elements-Eq-Rel (eq-rel-partition' (partition-Eq-Rel R)) R
  pr1
    ( relates-same-elements-eq-rel-partition-Eq-Rel' x y)
    ( ((C , I) , H) , p , q) =
    apply-universal-property-trunc-Prop
      ( H)
      ( prop-Eq-Rel R x y)
      ( λ (z , K) →
        trans-Eq-Rel R
          ( symm-Eq-Rel R (forward-implication (K x) p))
          ( forward-implication (K y) q))
  pr1 (pr1 (pr2 (relates-same-elements-eq-rel-partition-Eq-Rel' x y) r)) =
    inhabited-subtype-Eq-Rel R x
  pr2 (pr1 (pr2 (relates-same-elements-eq-rel-partition-Eq-Rel' x y) r)) =
    unit-trunc-Prop
      ( x , refl-has-same-elements-equivalence-class R (class R x))
  pr1 (pr2 (pr2 (relates-same-elements-eq-rel-partition-Eq-Rel' x y) r)) =
    refl-Eq-Rel R
  pr2 (pr2 (pr2 (relates-same-elements-eq-rel-partition-Eq-Rel' x y) r)) = r

  relates-same-elements-eq-rel-partition-Eq-Rel :
    relates-same-elements-Eq-Rel (eq-rel-partition (partition-Eq-Rel R)) R
  relates-same-elements-eq-rel-partition-Eq-Rel x y =
    logical-equivalence-reasoning
      ( sim-partition (partition-Eq-Rel R) x y)
      ↔ ( sim-partition' (partition-Eq-Rel R) x y)
        by
        ( iff-equiv
          ( inv-equiv (compute-sim-partition (partition-Eq-Rel R) x y)))
      ↔ ( sim-Eq-Rel R x y)
        by
        ( relates-same-elements-eq-rel-partition-Eq-Rel' x y)

issec-eq-rel-partition-Eq-Rel :
  {l : Level} {A : UU l} (R : Eq-Rel l A) →
  eq-rel-partition (partition-Eq-Rel R) ＝ R
issec-eq-rel-partition-Eq-Rel R =
  eq-relates-same-elements-Eq-Rel
    ( eq-rel-partition (partition-Eq-Rel R))
    ( R)
    ( relates-same-elements-eq-rel-partition-Eq-Rel R)
```


