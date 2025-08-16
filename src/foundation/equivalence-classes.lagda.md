# Equivalence classes

```agda
module foundation.equivalence-classes where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.inhabited-subtypes
open import foundation.locally-small-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.slice
open import foundation.small-types
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-image
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.embeddings
open import foundation-core.equivalence-relations
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.torsorial-type-families
```

</details>

## Idea

An equivalence class of an equivalence relation `R` on `A` is a subtype of `A`
that is merely equivalent to a subtype of the form `R x`. The type of
equivalence classes of an equivalence relation satisfies the universal property
of the set quotient.

## Definition

### The condition on subtypes of `A` of being an equivalence class

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-equivalence-class-Prop : subtype l2 A → Prop (l1 ⊔ l2)
  is-equivalence-class-Prop P =
    ∃ A (λ x → has-same-elements-subtype-Prop P (prop-equivalence-relation R x))

  is-equivalence-class : subtype l2 A → UU (l1 ⊔ l2)
  is-equivalence-class P = type-Prop (is-equivalence-class-Prop P)

  is-prop-is-equivalence-class :
    (P : subtype l2 A) → is-prop (is-equivalence-class P)
  is-prop-is-equivalence-class P =
    is-prop-type-Prop (is-equivalence-class-Prop P)
```

### The condition on inhabited subtypes of `A` of being an equivalence class

```agda
  is-equivalence-class-inhabited-subtype-equivalence-relation :
    subtype (l1 ⊔ l2) (inhabited-subtype l2 A)
  is-equivalence-class-inhabited-subtype-equivalence-relation Q =
    is-equivalence-class-Prop (subtype-inhabited-subtype Q)
```

### The type of equivalence classes

```agda
  equivalence-class : UU (l1 ⊔ lsuc l2)
  equivalence-class = type-subtype is-equivalence-class-Prop

  class : A → equivalence-class
  pr1 (class x) = prop-equivalence-relation R x
  pr2 (class x) =
    unit-trunc-Prop
      ( x , refl-has-same-elements-subtype (prop-equivalence-relation R x))

  emb-equivalence-class : equivalence-class ↪ subtype l2 A
  emb-equivalence-class = emb-subtype is-equivalence-class-Prop

  subtype-equivalence-class : equivalence-class → subtype l2 A
  subtype-equivalence-class = inclusion-subtype is-equivalence-class-Prop

  is-equivalence-class-equivalence-class :
    (C : equivalence-class) → is-equivalence-class (subtype-equivalence-class C)
  is-equivalence-class-equivalence-class =
    is-in-subtype-inclusion-subtype is-equivalence-class-Prop

  is-inhabited-subtype-equivalence-class :
    (C : equivalence-class) → is-inhabited-subtype (subtype-equivalence-class C)
  is-inhabited-subtype-equivalence-class (Q , H) =
    apply-universal-property-trunc-Prop H
      ( is-inhabited-subtype-Prop (subtype-equivalence-class (Q , H)))
      ( λ u →
        unit-trunc-Prop
          ( pr1 u ,
            backward-implication
              ( pr2 u (pr1 u))
              ( refl-equivalence-relation R (pr1 u))))

  inhabited-subtype-equivalence-class :
    (C : equivalence-class) → inhabited-subtype l2 A
  pr1 (inhabited-subtype-equivalence-class C) = subtype-equivalence-class C
  pr2 (inhabited-subtype-equivalence-class C) =
    is-inhabited-subtype-equivalence-class C

  is-in-equivalence-class : equivalence-class → (A → UU l2)
  is-in-equivalence-class P x = type-Prop (subtype-equivalence-class P x)

  abstract
    is-prop-is-in-equivalence-class :
      (x : equivalence-class) (a : A) →
      is-prop (is-in-equivalence-class x a)
    is-prop-is-in-equivalence-class P x =
      is-prop-type-Prop (subtype-equivalence-class P x)

  is-in-equivalence-class-Prop : equivalence-class → (A → Prop l2)
  pr1 (is-in-equivalence-class-Prop P x) = is-in-equivalence-class P x
  pr2 (is-in-equivalence-class-Prop P x) = is-prop-is-in-equivalence-class P x

  abstract
    is-set-equivalence-class : is-set equivalence-class
    is-set-equivalence-class =
      is-set-type-subtype is-equivalence-class-Prop is-set-subtype

  equivalence-class-Set : Set (l1 ⊔ lsuc l2)
  pr1 equivalence-class-Set = equivalence-class
  pr2 equivalence-class-Set = is-set-equivalence-class

  unit-im-equivalence-class :
    hom-slice (prop-equivalence-relation R) subtype-equivalence-class
  pr1 unit-im-equivalence-class = class
  pr2 unit-im-equivalence-class x = refl

  is-surjective-class : is-surjective class
  is-surjective-class C =
    map-trunc-Prop
      ( tot
        ( λ x p →
          inv
            ( eq-type-subtype
              ( is-equivalence-class-Prop)
              ( eq-has-same-elements-subtype
                ( pr1 C)
                ( prop-equivalence-relation R x)
                ( p)))))
      ( pr2 C)

  is-image-equivalence-class :
    is-image
      ( prop-equivalence-relation R)
      ( emb-equivalence-class)
      ( unit-im-equivalence-class)
  is-image-equivalence-class =
    is-image-is-surjective
      ( prop-equivalence-relation R)
      ( emb-equivalence-class)
      ( unit-im-equivalence-class)
      ( is-surjective-class)
```

## Properties

### Characterization of equality of equivalence classes

#### Equivalence classes are equal if they contain the same elements

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  has-same-elements-equivalence-class :
    (C D : equivalence-class R) → UU (l1 ⊔ l2)
  has-same-elements-equivalence-class C D =
    has-same-elements-subtype
      ( subtype-equivalence-class R C)
      ( subtype-equivalence-class R D)

  refl-has-same-elements-equivalence-class :
    (C : equivalence-class R) → has-same-elements-equivalence-class C C
  refl-has-same-elements-equivalence-class C =
    refl-has-same-elements-subtype (subtype-equivalence-class R C)

  is-torsorial-has-same-elements-equivalence-class :
    (C : equivalence-class R) →
    is-torsorial (has-same-elements-equivalence-class C)
  is-torsorial-has-same-elements-equivalence-class C =
    is-torsorial-Eq-subtype
      ( is-torsorial-has-same-elements-subtype
        ( subtype-equivalence-class R C))
      ( is-prop-is-equivalence-class R)
      ( subtype-equivalence-class R C)
      ( refl-has-same-elements-equivalence-class C)
      ( is-equivalence-class-equivalence-class R C)

  has-same-elements-eq-equivalence-class :
    (C D : equivalence-class R) → (C ＝ D) →
    has-same-elements-equivalence-class C D
  has-same-elements-eq-equivalence-class C .C refl =
    refl-has-same-elements-subtype (subtype-equivalence-class R C)

  is-equiv-has-same-elements-eq-equivalence-class :
    (C D : equivalence-class R) →
    is-equiv (has-same-elements-eq-equivalence-class C D)
  is-equiv-has-same-elements-eq-equivalence-class C =
    fundamental-theorem-id
      ( is-torsorial-has-same-elements-equivalence-class C)
      ( has-same-elements-eq-equivalence-class C)

  extensionality-equivalence-class :
    (C D : equivalence-class R) →
    (C ＝ D) ≃ has-same-elements-equivalence-class C D
  pr1 (extensionality-equivalence-class C D) =
    has-same-elements-eq-equivalence-class C D
  pr2 (extensionality-equivalence-class C D) =
    is-equiv-has-same-elements-eq-equivalence-class C D

  eq-has-same-elements-equivalence-class :
    (C D : equivalence-class R) →
    has-same-elements-equivalence-class C D → C ＝ D
  eq-has-same-elements-equivalence-class C D =
    map-inv-equiv (extensionality-equivalence-class C D)
```

#### Equivalence classes are equal if there exists an element contained in both

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  share-common-element-equivalence-class-Prop :
    (C D : equivalence-class R) → Prop (l1 ⊔ l2)
  share-common-element-equivalence-class-Prop C D =
    ∃ ( A)
      ( λ x →
        is-in-equivalence-class-Prop R C x ∧ is-in-equivalence-class-Prop R D x)

  share-common-element-equivalence-class :
    (C D : equivalence-class R) → UU (l1 ⊔ l2)
  share-common-element-equivalence-class C D =
    type-Prop (share-common-element-equivalence-class-Prop C D)

  abstract
    eq-share-common-element-equivalence-class :
      (C D : equivalence-class R) →
      share-common-element-equivalence-class C D → C ＝ D
    eq-share-common-element-equivalence-class C D H =
      apply-three-times-universal-property-trunc-Prop
        ( H)
        ( is-equivalence-class-equivalence-class R C)
        ( is-equivalence-class-equivalence-class R D)
        ( Id-Prop (equivalence-class-Set R) C D)
        ( λ (a , c , d) (v , φ) (w , ψ) →
          eq-has-same-elements-equivalence-class R C D
            ( λ x →
              logical-equivalence-reasoning
                is-in-equivalence-class R C x
                  ↔ sim-equivalence-relation R v x
                    by φ x
                  ↔ sim-equivalence-relation R a x
                    by iff-transitive-equivalence-relation R
                        ( symmetric-equivalence-relation
                            R _ _ (forward-implication (φ a) c))
                  ↔ sim-equivalence-relation R w x
                    by iff-transitive-equivalence-relation R
                        ( forward-implication (ψ a) d)
                  ↔ is-in-equivalence-class R D x
                    by inv-iff (ψ x)))

  eq-class-equivalence-class :
    (C : equivalence-class R) {a : A} →
    is-in-equivalence-class R C a → class R a ＝ C
  eq-class-equivalence-class C {a} H =
    eq-share-common-element-equivalence-class
      ( class R a)
      ( C)
      ( unit-trunc-Prop (a , refl-equivalence-relation R a , H))
```

### The type of equivalence classes containing a fixed element `a : A` is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A) (a : A)
  where

  center-total-is-in-equivalence-class :
    Σ (equivalence-class R) (λ P → is-in-equivalence-class R P a)
  pr1 center-total-is-in-equivalence-class = class R a
  pr2 center-total-is-in-equivalence-class = refl-equivalence-relation R a

  contraction-total-is-in-equivalence-class :
    ( t :
      Σ ( equivalence-class R)
        ( λ C → is-in-equivalence-class R C a)) →
    center-total-is-in-equivalence-class ＝ t
  contraction-total-is-in-equivalence-class (C , H) =
    eq-type-subtype
      ( λ D → is-in-equivalence-class-Prop R D a)
      ( eq-class-equivalence-class R C H)

  is-torsorial-is-in-equivalence-class :
    is-torsorial (λ P → is-in-equivalence-class R P a)
  pr1 is-torsorial-is-in-equivalence-class =
    center-total-is-in-equivalence-class
  pr2 is-torsorial-is-in-equivalence-class =
    contraction-total-is-in-equivalence-class

  is-in-equivalence-class-eq-equivalence-class :
    (q : equivalence-class R) → class R a ＝ q →
    is-in-equivalence-class R q a
  is-in-equivalence-class-eq-equivalence-class .(class R a) refl =
    refl-equivalence-relation R a

  abstract
    is-equiv-is-in-equivalence-class-eq-equivalence-class :
      (q : equivalence-class R) →
      is-equiv (is-in-equivalence-class-eq-equivalence-class q)
    is-equiv-is-in-equivalence-class-eq-equivalence-class =
      fundamental-theorem-id
        ( is-torsorial-is-in-equivalence-class)
        ( is-in-equivalence-class-eq-equivalence-class)
```

### Σ-decompositions of types induced by equivalence classes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  equiv-total-is-in-equivalence-class :
    Σ A (λ x → Σ (equivalence-class R) (λ X → is-in-equivalence-class R X x)) ≃ A
  equiv-total-is-in-equivalence-class =
    right-unit-law-Σ-is-contr
      ( is-torsorial-is-in-equivalence-class R)

  Σ-decomposition-is-in-equivalence-class :
    Σ (equivalence-class R) (type-subtype ∘ is-in-equivalence-class-Prop R) ≃ A
  Σ-decomposition-is-in-equivalence-class =
    equiv-total-is-in-equivalence-class ∘e equiv-left-swap-Σ
```

### The map `class : A → equivalence-class R` is an effective quotient map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  abstract
    effective-quotient' :
      (a : A) (q : equivalence-class R) →
      ( class R a ＝ q) ≃
      ( is-in-equivalence-class R q a)
    pr1 (effective-quotient' a q) =
      is-in-equivalence-class-eq-equivalence-class R a q
    pr2 (effective-quotient' a q) =
      is-equiv-is-in-equivalence-class-eq-equivalence-class R a q

  abstract
    eq-effective-quotient' :
      (a : A) (q : equivalence-class R) → is-in-equivalence-class R q a →
      class R a ＝ q
    eq-effective-quotient' a q =
      map-inv-is-equiv
        ( is-equiv-is-in-equivalence-class-eq-equivalence-class R a q)

  abstract
    is-effective-class :
      is-effective R (class R)
    is-effective-class x y =
      ( equiv-symmetric-equivalence-relation R) ∘e
      ( effective-quotient' x (class R y))

  abstract
    apply-effectiveness-class :
      {x y : A} → class R x ＝ class R y → sim-equivalence-relation R x y
    apply-effectiveness-class {x} {y} =
      map-equiv (is-effective-class x y)

  abstract
    apply-effectiveness-class' :
      {x y : A} → sim-equivalence-relation R x y → class R x ＝ class R y
    apply-effectiveness-class' {x} {y} =
      map-inv-equiv (is-effective-class x y)
```

### The map `class` into the type of equivalence classes is surjective and effective

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-surjective-and-effective-class :
    is-surjective-and-effective R (class R)
  pr1 is-surjective-and-effective-class =
    is-surjective-class R
  pr2 is-surjective-and-effective-class =
    is-effective-class R
```

### The map `class` into the type of equivalence classes is a reflecting map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  quotient-reflecting-map-equivalence-class :
    reflecting-map-equivalence-relation R (equivalence-class R)
  pr1 quotient-reflecting-map-equivalence-class =
    class R
  pr2 quotient-reflecting-map-equivalence-class =
    apply-effectiveness-class' R
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  transitive-is-in-equivalence-class :
    (P : equivalence-class R) (a b : A) →
    is-in-equivalence-class R P a → sim-equivalence-relation R a b →
    is-in-equivalence-class R P b
  transitive-is-in-equivalence-class P a b p r =
    apply-universal-property-trunc-Prop
      ( is-equivalence-class-equivalence-class R P)
      ( subtype-equivalence-class R P b)
      ( λ (x , H) →
        backward-implication
          ( H b)
          ( transitive-equivalence-relation R _ a b
            ( r)
            ( forward-implication (H a) p)))
```

### The type of equivalence classes is locally small

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-locally-small-equivalence-class :
    is-locally-small (l1 ⊔ l2) (equivalence-class R)
  is-locally-small-equivalence-class C D =
    is-small-equiv
      ( has-same-elements-equivalence-class R C D)
      ( extensionality-equivalence-class R C D)
      ( is-small-Π
        ( is-small')
        ( λ x → is-small-logical-equivalence is-small' is-small'))
```

### The type of equivalence classes is small

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-small-equivalence-class : is-small (l1 ⊔ l2) (equivalence-class R)
  is-small-equivalence-class =
    is-small-is-surjective
      ( is-surjective-class R)
      ( is-small-lmax l2 A)
      ( is-locally-small-equivalence-class R)

  equivalence-class-Small-Type : Small-Type (l1 ⊔ l2) (l1 ⊔ lsuc l2)
  pr1 equivalence-class-Small-Type = equivalence-class R
  pr2 equivalence-class-Small-Type = is-small-equivalence-class

  small-equivalence-class : UU (l1 ⊔ l2)
  small-equivalence-class =
    small-type-Small-Type equivalence-class-Small-Type
```
