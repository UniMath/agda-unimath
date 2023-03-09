# Equivalence relations

```agda
module foundation.equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.equivalence-relations public

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.equational-reasoning
open import foundation.equivalence-classes
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.full-subtypes
open import foundation.functions
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.partitions
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-quotients
open import foundation.sets
open import foundation.sigma-decompositions
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.uniqueness-set-quotients
open import foundation.universal-property-set-quotients

open import foundation-core.universe-levels
```

</details>

## Properties

### Characterization of equality in the type of equivalence relations

```agda
relate-same-elements-Eq-Rel :
  {l1 l2 l3 : Level} {A : UU l1} → Eq-Rel l2 A → Eq-Rel l3 A → UU (l1 ⊔ l2 ⊔ l3)
relate-same-elements-Eq-Rel R S =
  relates-same-elements-Rel-Prop (prop-Eq-Rel R) (prop-Eq-Rel S)

module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  refl-relate-same-elements-Eq-Rel : relate-same-elements-Eq-Rel R R
  refl-relate-same-elements-Eq-Rel =
    refl-relates-same-elements-Rel-Prop (prop-Eq-Rel R)

  is-contr-total-relate-same-elements-Eq-Rel :
    is-contr (Σ (Eq-Rel l2 A) (relate-same-elements-Eq-Rel R))
  is-contr-total-relate-same-elements-Eq-Rel =
    is-contr-total-Eq-subtype
      ( is-contr-total-relates-same-elements-Rel-Prop (prop-Eq-Rel R))
      ( is-prop-is-equivalence-relation)
      ( prop-Eq-Rel R)
      ( refl-relate-same-elements-Eq-Rel)
      ( is-equivalence-relation-prop-Eq-Rel R)

  relate-same-elements-eq-Eq-Rel :
    (S : Eq-Rel l2 A) → (R ＝ S) → relate-same-elements-Eq-Rel R S
  relate-same-elements-eq-Eq-Rel .R refl = refl-relate-same-elements-Eq-Rel

  is-equiv-relate-same-elements-eq-Eq-Rel :
    (S : Eq-Rel l2 A) → is-equiv (relate-same-elements-eq-Eq-Rel S)
  is-equiv-relate-same-elements-eq-Eq-Rel =
    fundamental-theorem-id
      is-contr-total-relate-same-elements-Eq-Rel
      relate-same-elements-eq-Eq-Rel

  extensionality-Eq-Rel :
    (S : Eq-Rel l2 A) → (R ＝ S) ≃ relate-same-elements-Eq-Rel R S
  pr1 (extensionality-Eq-Rel S) = relate-same-elements-eq-Eq-Rel S
  pr2 (extensionality-Eq-Rel S) = is-equiv-relate-same-elements-eq-Eq-Rel S

  eq-relate-same-elements-Eq-Rel :
    (S : Eq-Rel l2 A) → relate-same-elements-Eq-Rel R S → (R ＝ S)
  eq-relate-same-elements-Eq-Rel S =
    map-inv-equiv (extensionality-Eq-Rel S)
```

### The type of equivalence relations on `A` is equivalent to the type of partitions on `A`

#### The partition obtained from an equivalence relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  is-block-partition-Eq-Rel-Prop : subtype (l1 ⊔ l2) (inhabited-subtype l2 A)
  is-block-partition-Eq-Rel-Prop Q =
    is-equivalence-class-Prop R (subtype-inhabited-subtype Q)

  is-block-partition-Eq-Rel : inhabited-subtype l2 A → UU (l1 ⊔ l2)
  is-block-partition-Eq-Rel Q = type-Prop (is-block-partition-Eq-Rel-Prop Q)

  is-partition-is-equivalence-class-inhabited-subtype-Eq-Rel :
    is-partition (is-equivalence-class-inhabited-subtype-Eq-Rel R)
  is-partition-is-equivalence-class-inhabited-subtype-Eq-Rel x =
    is-contr-equiv
      ( Σ ( Σ ( equivalence-class R)
              ( λ C → is-in-equivalence-class R C x))
          ( λ t → is-inhabited-subtype (subtype-equivalence-class R (pr1 t))))
      ( ( equiv-right-swap-Σ) ∘e
        ( equiv-Σ
          ( λ Q → is-in-subtype (subtype-equivalence-class R (pr1 Q)) x)
          ( equiv-right-swap-Σ)
          ( λ Q → id-equiv)))
      ( is-contr-Σ
        ( is-contr-total-is-in-equivalence-class R x)
        ( center-total-is-in-equivalence-class R x)
        ( is-proof-irrelevant-is-prop
          ( is-prop-type-trunc-Prop)
          ( is-inhabited-subtype-equivalence-class R (class R x))))

  partition-Eq-Rel : partition l2 (l1 ⊔ l2) A
  pr1 partition-Eq-Rel = is-block-partition-Eq-Rel-Prop
  pr2 partition-Eq-Rel =
    is-partition-is-equivalence-class-inhabited-subtype-Eq-Rel

  equiv-block-equivalence-class :
    equivalence-class R ≃ block-partition partition-Eq-Rel
  equiv-block-equivalence-class =
    ( compute-block-partition partition-Eq-Rel) ∘e
    ( ( equiv-right-swap-Σ) ∘e
      ( inv-equiv
        ( equiv-inclusion-is-full-subtype
          ( is-inhabited-subtype-Prop ∘ subtype-equivalence-class R)
          ( is-inhabited-subtype-equivalence-class R))))
```

#### The equivalence relation obtained from a partition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  where

  sim-partition : A → A → UU (l1 ⊔ l2)
  sim-partition x y =
    Σ ( block-partition P)
      ( λ Q → is-in-block-partition P Q x × is-in-block-partition P Q y)

  is-proof-irrelevant-sim-partition :
    (x y : A) → is-proof-irrelevant (sim-partition x y)
  is-proof-irrelevant-sim-partition x y (Q , p , q) =
    is-contr-equiv'
      ( Σ ( Σ ( block-partition P)
              ( λ B → is-in-block-partition P B x))
          ( λ B → is-in-block-partition P (pr1 B) y))
      ( assoc-Σ
        ( block-partition P)
        ( λ U → is-in-block-partition P U x)
        ( λ U → is-in-block-partition P (pr1 U) y))
      ( is-contr-Σ
        ( is-contr-block-containing-element-partition P x)
        ( pair Q p)
        ( is-proof-irrelevant-is-prop
          ( is-prop-is-in-block-partition P Q y)
          ( q)))

  is-prop-sim-partition : (x y : A) → is-prop (sim-partition x y)
  is-prop-sim-partition x y =
    is-prop-is-proof-irrelevant (is-proof-irrelevant-sim-partition x y)

  prop-eq-rel-partition : Rel-Prop (l1 ⊔ l2) A
  pr1 (prop-eq-rel-partition x y) = sim-partition x y
  pr2 (prop-eq-rel-partition x y) = is-prop-sim-partition x y

  refl-sim-partition : {x : A} → sim-partition x x
  pr1 (refl-sim-partition {x}) = class-partition P x
  pr1 (pr2 (refl-sim-partition {x})) = is-in-block-class-partition P x
  pr2 (pr2 (refl-sim-partition {x})) = is-in-block-class-partition P x

  symm-sim-partition : {x y : A} → sim-partition x y → sim-partition y x
  pr1 (symm-sim-partition {x} {y} (Q , p , q)) = Q
  pr1 (pr2 (symm-sim-partition {x} {y} (Q , p , q))) = q
  pr2 (pr2 (symm-sim-partition {x} {y} (Q , p , q))) = p

  trans-sim-partition :
    {x y z : A} → sim-partition x y → sim-partition y z → sim-partition x z
  pr1 (trans-sim-partition {x} {y} {z} (Q1 , p1 , q1) (Q2 , p2 , q2)) = Q1
  pr1
    ( pr2
      ( trans-sim-partition (B , p , q) (B' , p' , q'))) = p
  pr2 (pr2 (trans-sim-partition {x} {y} {z} (B , p , q) (B' , p' , q'))) =
    backward-implication
      ( has-same-elements-eq-inhabited-subtype
        ( inhabited-subtype-block-partition P B)
        ( inhabited-subtype-block-partition P B')
        ( ap
          ( inhabited-subtype-block-partition P)
          ( ap
            ( pr1)
            ( eq-is-contr
              ( is-contr-block-containing-element-partition P y)
              { B , q}
              { B' , p'})))
        ( z))
      ( q')

  eq-rel-partition : Eq-Rel (l1 ⊔ l2) A
  pr1 eq-rel-partition = prop-eq-rel-partition
  pr1 (pr2 eq-rel-partition) = refl-sim-partition
  pr1 (pr2 (pr2 eq-rel-partition)) = symm-sim-partition
  pr2 (pr2 (pr2 eq-rel-partition)) = trans-sim-partition

  is-inhabited-subtype-prop-eq-rel-partition :
    (a : A) → is-inhabited-subtype (prop-eq-rel-partition a)
  is-inhabited-subtype-prop-eq-rel-partition a =
    unit-trunc-Prop (a , refl-sim-partition)

  inhabited-subtype-eq-rel-partition :
    (a : A) → inhabited-subtype (l1 ⊔ l2) A
  pr1 (inhabited-subtype-eq-rel-partition a) = prop-eq-rel-partition a
  pr2 (inhabited-subtype-eq-rel-partition a) =
    is-inhabited-subtype-prop-eq-rel-partition a

  is-block-inhabited-subtype-eq-rel-partition :
    (a : A) →
    is-block-partition
      ( partition-Eq-Rel eq-rel-partition)
      ( inhabited-subtype-eq-rel-partition a)
  is-block-inhabited-subtype-eq-rel-partition a =
    unit-trunc-Prop (a , λ x → pair id id)
```

#### The equivalence relation obtained from the partition induced by an equivalence relation `R` is `R` itself

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  relate-same-elements-eq-rel-partition-Eq-Rel :
    relate-same-elements-Eq-Rel (eq-rel-partition (partition-Eq-Rel R)) R
  pr1
    ( relate-same-elements-eq-rel-partition-Eq-Rel x y)
    ( C , p , q) =
    apply-universal-property-trunc-Prop
      ( is-block-inhabited-subtype-block-partition (partition-Eq-Rel R) C)
      ( prop-Eq-Rel R x y)
      ( λ (z , K) →
        trans-Eq-Rel R
          ( symm-Eq-Rel R (forward-implication (K x) p))
          ( forward-implication (K y) q))
  pr1 (pr2 (relate-same-elements-eq-rel-partition-Eq-Rel x y) r) =
    make-block-partition
      ( partition-Eq-Rel R)
      ( inhabited-subtype-equivalence-class R (class R x))
      ( is-equivalence-class-equivalence-class R (class R x))
  pr1 (pr2 (pr2 (relate-same-elements-eq-rel-partition-Eq-Rel x y) r)) =
    make-is-in-block-partition
      ( partition-Eq-Rel R)
      ( inhabited-subtype-equivalence-class R (class R x))
      ( is-equivalence-class-equivalence-class R (class R x))
      ( x)
      ( refl-Eq-Rel R)
  pr2 (pr2 (pr2 (relate-same-elements-eq-rel-partition-Eq-Rel x y) r)) =
    make-is-in-block-partition
      ( partition-Eq-Rel R)
      ( inhabited-subtype-equivalence-class R (class R x))
      ( is-equivalence-class-equivalence-class R (class R x))
      ( y)
      ( r)

issec-eq-rel-partition-Eq-Rel :
  {l : Level} {A : UU l} (R : Eq-Rel l A) →
  eq-rel-partition (partition-Eq-Rel R) ＝ R
issec-eq-rel-partition-Eq-Rel R =
  eq-relate-same-elements-Eq-Rel
    ( eq-rel-partition (partition-Eq-Rel R))
    ( R)
    ( relate-same-elements-eq-rel-partition-Eq-Rel R)
```

#### The partition obtained from the equivalence relation induced by a partition is the partition itself

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : partition l1 l2 A)
  where

  is-block-is-equivalence-class-eq-rel-partition :
    (Q : inhabited-subtype l1 A) →
    is-equivalence-class (eq-rel-partition P) (subtype-inhabited-subtype Q) →
    is-block-partition P Q
  is-block-is-equivalence-class-eq-rel-partition Q H =
    apply-universal-property-trunc-Prop H
      ( subtype-partition P Q)
      ( λ (a , K) →
        tr
          ( is-block-partition P)
          ( inv
            ( eq-has-same-elements-inhabited-subtype Q
              ( inhabited-subtype-block-partition P (class-partition P a))
              ( λ x →
                logical-equivalence-reasoning
                  is-in-inhabited-subtype Q x
                    ↔ Σ ( block-partition P)
                        ( λ B →
                          is-in-block-partition P B a ×
                          is-in-block-partition P B x)
                      by K x
                    ↔ is-in-block-partition P (class-partition P a) x
                      by
                      iff-equiv
                        ( ( left-unit-law-Σ-is-contr
                            ( is-contr-block-containing-element-partition P a)
                            ( center-block-containing-element-partition P a)) ∘e
                          ( inv-assoc-Σ
                            ( block-partition P)
                            ( λ B → is-in-block-partition P B a)
                            ( λ B → is-in-block-partition P (pr1 B) x))))))
          ( is-block-class-partition P a))

  is-equivalence-class-is-block-partition :
    (Q : inhabited-subtype l1 A) →
    is-block-partition P Q →
    is-equivalence-class (eq-rel-partition P) (subtype-inhabited-subtype Q)
  is-equivalence-class-is-block-partition Q H =
    apply-universal-property-trunc-Prop
      ( is-inhabited-subtype-inhabited-subtype Q)
      ( is-equivalence-class-Prop
        ( eq-rel-partition P)
        ( subtype-inhabited-subtype Q))
      ( λ (a , q) →
        unit-trunc-Prop
          ( pair
            ( a)
            ( λ x →
              iff-equiv
              ( equivalence-reasoning
                is-in-inhabited-subtype Q x
                  ≃ is-in-block-partition P (make-block-partition P Q H) x
                    by
                    compute-is-in-block-partition P Q H x
                  ≃ Σ ( block-partition P)
                      ( λ B →
                        is-in-block-partition P B a ×
                        is-in-block-partition P B x)
                    by
                    inv-equiv
                      ( ( left-unit-law-Σ-is-contr
                          ( is-contr-block-containing-element-partition P a)
                          ( pair
                            ( make-block-partition P Q H)
                            ( make-is-in-block-partition P Q H a q))) ∘e
                        ( inv-assoc-Σ
                          ( block-partition P)
                          ( λ B → is-in-block-partition P B a)
                          ( λ B → is-in-block-partition P (pr1 B) x)))))))

  has-same-elements-partition-eq-rel-partition :
    has-same-elements-subtype
      ( subtype-partition (partition-Eq-Rel (eq-rel-partition P)))
      ( subtype-partition P)
  pr1 (has-same-elements-partition-eq-rel-partition Q) H =
    is-block-is-equivalence-class-eq-rel-partition Q H
  pr2 (has-same-elements-partition-eq-rel-partition Q) H =
    is-equivalence-class-is-block-partition Q H

isretr-eq-rel-partition-Eq-Rel :
  {l : Level} {A : UU l} (P : partition l l A) →
  partition-Eq-Rel (eq-rel-partition P) ＝ P
isretr-eq-rel-partition-Eq-Rel P =
  eq-has-same-blocks-partition
    ( partition-Eq-Rel (eq-rel-partition P))
    ( P)
    ( has-same-elements-partition-eq-rel-partition P)
```

#### The map `eq-rel-partition` is an equivalence

```agda
is-equiv-eq-rel-partition :
  {l : Level} {A : UU l} → is-equiv (eq-rel-partition {l} {l} {l} {A})
is-equiv-eq-rel-partition =
  is-equiv-has-inverse
    partition-Eq-Rel
    issec-eq-rel-partition-Eq-Rel
    isretr-eq-rel-partition-Eq-Rel

equiv-eq-rel-partition :
  {l : Level} {A : UU l} → partition l l A ≃ Eq-Rel l A
pr1 equiv-eq-rel-partition = eq-rel-partition
pr2 equiv-eq-rel-partition = is-equiv-eq-rel-partition
```

### Equivalence relations are equivalent to set-indexed Σ-decompositions

#### The Σ-decomposition obtained from an equivalence relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  set-indexed-Σ-decomposition-Eq-Rel :
    Set-Indexed-Σ-Decomposition (l1 ⊔ l2) (l1 ⊔ l2) A
  set-indexed-Σ-decomposition-Eq-Rel =
    set-indexed-Σ-decomposition-partition (partition-Eq-Rel R)
```

### The type of equivalence relations on `A` is equivalent to the type of sets `X` equipped with a surjective map from `A` into `X`

#### The surjection into a set obtained from an equivalence relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  surjection-into-set-Eq-Rel :
    Surjection-Into-Set (l1 ⊔ l2) A
  pr1 surjection-into-set-Eq-Rel = quotient-Set R
  pr2 surjection-into-set-Eq-Rel = surjection-quotient-map R
```

#### The equivalence relation obtained from a surjection into a set

```agda
module _
  {l1 l2 : Level} {A : UU l1} (X : Set l2) (f : A → type-Set X)
  where

  rel-map-into-set : Rel-Prop l2 A
  rel-map-into-set x y = Id-Prop X (f x) (f y)

  sim-map-into-set : Rel l2 A
  sim-map-into-set x y = type-Prop (rel-map-into-set x y)

  refl-sim-map-into-set : is-reflexive sim-map-into-set
  refl-sim-map-into-set x = refl

  symm-sim-map-into-set : is-symmetric sim-map-into-set
  symm-sim-map-into-set x y H = inv H

  trans-sim-map-into-set : is-transitive sim-map-into-set
  trans-sim-map-into-set x y z H K = H ∙ K

  eq-rel-map-into-set : Eq-Rel l2 A
  pr1 eq-rel-map-into-set = rel-map-into-set
  pr1 (pr2 eq-rel-map-into-set) {x} = refl-sim-map-into-set x
  pr1 (pr2 (pr2 eq-rel-map-into-set)) {x} {y} = symm-sim-map-into-set x y
  pr2 (pr2 (pr2 eq-rel-map-into-set)) {x} {y} {z} = trans-sim-map-into-set x y z

  is-effective-map-into-set :
    is-effective eq-rel-map-into-set f
  is-effective-map-into-set x y = id-equiv

eq-rel-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} → Surjection-Into-Set l2 A → Eq-Rel l2 A
eq-rel-Surjection-Into-Set f =
  eq-rel-map-into-set
    ( set-Surjection-Into-Set f)
    ( map-Surjection-Into-Set f)

is-effective-map-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A) →
  is-effective (eq-rel-Surjection-Into-Set f) (map-Surjection-Into-Set f)
is-effective-map-Surjection-Into-Set f =
  is-effective-map-into-set
    ( set-Surjection-Into-Set f)
    ( map-Surjection-Into-Set f)
```

#### The equivalence relation obtained from the quotient map induced by an equivalence relation is that same equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  relate-same-elements-eq-rel-surjection-into-set-Eq-Rel :
    relate-same-elements-Eq-Rel
      ( eq-rel-Surjection-Into-Set (surjection-into-set-Eq-Rel R))
      ( R)
  relate-same-elements-eq-rel-surjection-into-set-Eq-Rel x y =
    iff-equiv (is-effective-quotient-map R x y)

isretr-eq-rel-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel (l1 ⊔ l2) A) →
  eq-rel-Surjection-Into-Set (surjection-into-set-Eq-Rel R) ＝ R
isretr-eq-rel-Surjection-Into-Set R =
  eq-relate-same-elements-Eq-Rel
    ( eq-rel-Surjection-Into-Set (surjection-into-set-Eq-Rel R))
    ( R)
    ( relate-same-elements-eq-rel-surjection-into-set-Eq-Rel R)
```

#### The surjection into a set obtained from the equivalence relation induced by a surjection into a set is the original surjection into a set

```agda
equiv-surjection-into-set-eq-rel-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A) →
  equiv-Surjection-Into-Set
    ( surjection-into-set-Eq-Rel (eq-rel-Surjection-Into-Set f))
    ( f)
equiv-surjection-into-set-eq-rel-Surjection-Into-Set f =
  center
    ( uniqueness-set-quotient
      ( eq-rel-Surjection-Into-Set f)
      ( quotient-Set (eq-rel-Surjection-Into-Set f))
      ( reflecting-map-quotient-map (eq-rel-Surjection-Into-Set f))
      ( is-set-quotient-set-quotient (eq-rel-Surjection-Into-Set f))
      ( set-Surjection-Into-Set f)
      ( pair
        ( map-Surjection-Into-Set f)
        ( λ H → H))
      ( is-set-quotient-is-surjective-and-effective
        ( eq-rel-Surjection-Into-Set f)
        ( set-Surjection-Into-Set f)
        ( pr1 (pr2 f) , (λ {x} {y} z → z))
        ( pair
          ( is-surjective-Surjection-Into-Set f)
          ( is-effective-map-Surjection-Into-Set f))))

issec-eq-rel-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set (l1 ⊔ l2) A) →
  surjection-into-set-Eq-Rel (eq-rel-Surjection-Into-Set f) ＝ f
issec-eq-rel-Surjection-Into-Set f =
  eq-equiv-Surjection-Into-Set
    ( surjection-into-set-Eq-Rel (eq-rel-Surjection-Into-Set f))
    ( f)
    ( equiv-surjection-into-set-eq-rel-Surjection-Into-Set f)
```

#### The type of equivalence relations on `A` is equivalent to the type of surjections from `A` into a set.

```agda
is-equiv-surjection-into-set-Eq-Rel :
  {l1 : Level} {A : UU l1} →
  is-equiv (surjection-into-set-Eq-Rel {l1} {l1} {A})
is-equiv-surjection-into-set-Eq-Rel {l1} {A} =
  is-equiv-has-inverse
    ( eq-rel-Surjection-Into-Set {l1} {l1} {A})
    ( issec-eq-rel-Surjection-Into-Set {l1} {l1} {A})
    ( isretr-eq-rel-Surjection-Into-Set {l1} {l1} {A})

equiv-surjection-into-set-Eq-Rel :
  {l1 : Level} (A : UU l1) →
  Eq-Rel l1 A ≃ Surjection-Into-Set l1 A
pr1 (equiv-surjection-into-set-Eq-Rel A) =
  surjection-into-set-Eq-Rel
pr2 (equiv-surjection-into-set-Eq-Rel A) =
  is-equiv-surjection-into-set-Eq-Rel
```
