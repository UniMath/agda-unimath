# The subtractive closure of ideals of semirings

```agda
module ring-theory.subtractive-closure-ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.propositional-truncations
open import foundation.similarity-subtypes
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.submonoids

open import order-theory.galois-connections-large-posets
open import order-theory.least-upper-bounds-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.order-preserving-maps-large-posets
open import order-theory.reflective-galois-connections-large-posets

open import ring-theory.ideals-semirings
open import ring-theory.joins-ideals-semirings
open import ring-theory.poset-of-ideals-semirings
open import ring-theory.poset-of-subtractive-ideals-semirings
open import ring-theory.semirings
open import ring-theory.subsets-semirings
open import ring-theory.subtractive-ideals-semirings
```

</details>

## Idea

The {{#concept "subtractive closure" Disambiguation="ideal of a semiring" Agda=subtractive-closure-ideal-Semiring}} of an [ideal](ring-theory.ideals-semirings.md) `I` of a [semiring](ring-theory.semirings.md) `R` is the least [subtractive ideal](ring-theory.subtractive-ideals-semirings.lagda.md) containing `I`. More concretely, the subtractive closure `S(I)` consists of those elements `x : R` for which there [exists](foundation.existential-quantification.md) an `y ∈ I` such that `x + y ∈ I`.

**Theorem** Consider an ideal `I` of `R`. Then the set `S(I)` consisting of `x : R` for which there exists an element `y ∈ I` such that `x + y ∈ I` is a subtractive ideal.

*Proof.*
- Note that `0 ∈ S(I)` since `0 ∈ I` and `0 + 0 ∈ I`.
- If `x y ∈ S(I)` with `u v ∈ I` such that `x + u ∈ I` and `y + v ∈ I`, then `u + v ∈ I` and `(x + y) + (u + v) = (x + u) + (y + v) ∈ I`.
- If `x z : R` and `y ∈ S(I)` with `u ∈ I` such that `y + u ∈ I`, then we have `(xu)z ∈ I` and `(x(y+u))z = (xy)z + (xu)z ∈ I`.
- If `x (x + y) ∈ S(I)` with `u v ∈ I` such that `x + u ∈ I` and `(x + y) + v ∈ I`, then we have `x + (v + u) ∈ I` and `y + (x + (v + u)) = ((x + y) + v) + u ∈ I`.

The universal property of the subtractive closure `S(I)` of `I` states that for any subtractive ideal `J` we have the following [logical equivalence](foundation.logical-equivalences.md):

```text
  S(I) ⊆ J ⇔ I ⊆ J.
```

Thus, there is a [large Galois connection](order-theory.galois-connections.md) between the [large poset](order-theory.large-posets.md) of ideals of `R` and the poset of subtractive ideals of `R`.

## Definitions

### The universal property of the subtractive closure

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  (I : ideal-Semiring l2 R) (I' : subtractive-ideal-Semiring l3 R)
  where

  is-subtractive-closure-ideal-Semiring : UUω
  is-subtractive-closure-ideal-Semiring =
    {l4 : Level} (J : subtractive-ideal-Semiring l4 R) →
    leq-subtractive-ideal-Semiring R I' J ↔
    leq-ideal-Semiring R I (ideal-subtractive-ideal-Semiring R J)

  contains-ideal-is-subtractive-closure-ideal-Semiring :
    is-subtractive-closure-ideal-Semiring →
    leq-ideal-Semiring R I (ideal-subtractive-ideal-Semiring R I')
  contains-ideal-is-subtractive-closure-ideal-Semiring U =
    forward-implication (U I') (refl-leq-subtractive-ideal-Semiring R I')

  leq-is-subtractive-closure-ideal-Semiring :
    is-subtractive-closure-ideal-Semiring →
    {l4 : Level} (J : subtractive-ideal-Semiring l4 R) →
    leq-ideal-Semiring R I (ideal-subtractive-ideal-Semiring R J) →
    leq-subtractive-ideal-Semiring R I' J
  leq-is-subtractive-closure-ideal-Semiring U J =
    backward-implication (U J)
```

### The universal property of the subtractive closure of a family of ideals of a semiring

```agda
module _
  {l1 l2 l3 l4 : Level} (R : Semiring l1) {U : UU l2}
  (I : U → ideal-Semiring l3 R)
  (J : subtractive-ideal-Semiring l4 R)
  (H :
    (α : U) → leq-ideal-Semiring R (I α) (ideal-subtractive-ideal-Semiring R J))
  where

  is-subtractive-ideal-generated-by-family-of-ideals-Semiring : UUω
  is-subtractive-ideal-generated-by-family-of-ideals-Semiring =
    {l : Level} (K : subtractive-ideal-Semiring l R) →
    ( (α : U) →
      leq-ideal-Semiring R (I α) (ideal-subtractive-ideal-Semiring R K)) →
    leq-subtractive-ideal-Semiring R J K
```


### Construction of the subtractive closure Galois connection

#### The subtractive closure of an ideal

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : ideal-Semiring l2 R)
  where

  subset-subtractive-closure-ideal-Semiring :
    subset-Semiring (l1 ⊔ l2) R
  subset-subtractive-closure-ideal-Semiring x =
    ∃ ( type-Semiring R)
      ( λ y →
        subset-ideal-Semiring R I y ∧
        subset-ideal-Semiring R I (add-Semiring R x y))

  is-in-subtractive-closure-ideal-Semiring : type-Semiring R → UU (l1 ⊔ l2)
  is-in-subtractive-closure-ideal-Semiring =
    is-in-subset-Semiring R subset-subtractive-closure-ideal-Semiring

  is-prop-is-in-subtractive-closure-ideal-Semiring :
    (x : type-Semiring R) → is-prop (is-in-subtractive-closure-ideal-Semiring x)
  is-prop-is-in-subtractive-closure-ideal-Semiring =
    is-prop-is-in-subset-Semiring R subset-subtractive-closure-ideal-Semiring

  type-subtractive-closure-ideal-Semiring : UU (l1 ⊔ l2)
  type-subtractive-closure-ideal-Semiring =
    type-subset-Semiring R subset-subtractive-closure-ideal-Semiring

  inclusion-subtractive-closure-ideal-Semiring :
    type-subtractive-closure-ideal-Semiring → type-Semiring R
  inclusion-subtractive-closure-ideal-Semiring =
    inclusion-subset-Semiring R subset-subtractive-closure-ideal-Semiring

  ap-inclusion-subtractive-closure-ideal-Semiring :
    (x y : type-subtractive-closure-ideal-Semiring) → x ＝ y →
    inclusion-subtractive-closure-ideal-Semiring x ＝
    inclusion-subtractive-closure-ideal-Semiring y
  ap-inclusion-subtractive-closure-ideal-Semiring =
    ap-inclusion-subset-Semiring R subset-subtractive-closure-ideal-Semiring

  is-in-subset-inclusion-subtractive-closure-ideal-Semiring :
    (x : type-subtractive-closure-ideal-Semiring) →
    is-in-subtractive-closure-ideal-Semiring
      ( inclusion-subtractive-closure-ideal-Semiring x)
  is-in-subset-inclusion-subtractive-closure-ideal-Semiring =
    is-in-subset-inclusion-subset-Semiring R
      subset-subtractive-closure-ideal-Semiring

  is-closed-under-eq-subtractive-closure-ideal-Semiring :
    {x y : type-Semiring R} → is-in-subtractive-closure-ideal-Semiring x →
    (x ＝ y) → is-in-subtractive-closure-ideal-Semiring y
  is-closed-under-eq-subtractive-closure-ideal-Semiring =
    is-closed-under-eq-subset-Semiring R
      subset-subtractive-closure-ideal-Semiring

  is-closed-under-eq-subtractive-closure-ideal-Semiring' :
    {x y : type-Semiring R} → is-in-subtractive-closure-ideal-Semiring y →
    (x ＝ y) → is-in-subtractive-closure-ideal-Semiring x
  is-closed-under-eq-subtractive-closure-ideal-Semiring' =
    is-closed-under-eq-subset-Semiring' R
      subset-subtractive-closure-ideal-Semiring

  contains-ideal-subtractive-closure-ideal-Semiring :
    subset-ideal-Semiring R I ⊆ subset-subtractive-closure-ideal-Semiring
  contains-ideal-subtractive-closure-ideal-Semiring x H =
    intro-exists
      ( zero-Semiring R)
      ( contains-zero-ideal-Semiring R I ,
        is-closed-under-addition-ideal-Semiring R I H
          ( contains-zero-ideal-Semiring R I))

  contains-zero-subtractive-closure-ideal-Semiring :
    is-in-subtractive-closure-ideal-Semiring (zero-Semiring R)
  contains-zero-subtractive-closure-ideal-Semiring =
    contains-ideal-subtractive-closure-ideal-Semiring _
      ( contains-zero-ideal-Semiring R I)

  is-closed-under-addition-subtractive-closure-ideal-Semiring :
    {x y : type-Semiring R} →
    is-in-subtractive-closure-ideal-Semiring x →
    is-in-subtractive-closure-ideal-Semiring y →
    is-in-subtractive-closure-ideal-Semiring (add-Semiring R x y)
  is-closed-under-addition-subtractive-closure-ideal-Semiring H K =
    apply-twice-universal-property-trunc-Prop H K
      ( subset-subtractive-closure-ideal-Semiring (add-Semiring R _ _))
      ( λ (u , u∈I , x+u∈I) (v , v∈I , y+v∈I) →
        intro-exists
          ( add-Semiring R u v)
          ( is-closed-under-addition-ideal-Semiring R I u∈I v∈I ,
            is-closed-under-eq-ideal-Semiring R I
              ( is-closed-under-addition-ideal-Semiring R I x+u∈I y+v∈I)
              ( interchange-add-add-Semiring R)))

  is-additive-submonoid-subtractive-closure-ideal-Semiring :
    is-additive-submonoid-subset-Semiring R
      subset-subtractive-closure-ideal-Semiring
  pr1 is-additive-submonoid-subtractive-closure-ideal-Semiring =
    contains-zero-subtractive-closure-ideal-Semiring
  pr2 is-additive-submonoid-subtractive-closure-ideal-Semiring =
    is-closed-under-addition-subtractive-closure-ideal-Semiring

  additive-submonoid-subtractive-closure-ideal-Semiring :
    Submonoid (l1 ⊔ l2) (additive-monoid-Semiring R)
  pr1 additive-submonoid-subtractive-closure-ideal-Semiring =
    subset-subtractive-closure-ideal-Semiring
  pr2 additive-submonoid-subtractive-closure-ideal-Semiring =
    is-additive-submonoid-subtractive-closure-ideal-Semiring

  is-closed-under-left-multiplication-subtractive-closure-ideal-Semiring :
    is-closed-under-left-multiplication-subset-Semiring R
      subset-subtractive-closure-ideal-Semiring
  is-closed-under-left-multiplication-subtractive-closure-ideal-Semiring H =
    apply-universal-property-trunc-Prop H
      ( subset-subtractive-closure-ideal-Semiring _)
      ( λ (u , u∈I , y+u∈I) →
        intro-exists
          ( mul-Semiring R _ u)
          ( is-closed-under-left-multiplication-ideal-Semiring R I u∈I ,
            is-closed-under-eq-ideal-Semiring R I
              ( is-closed-under-left-multiplication-ideal-Semiring R I y+u∈I)
              ( left-distributive-mul-add-Semiring R _ _ _)))

  is-closed-under-right-multiplication-subtractive-closure-ideal-Semiring :
    is-closed-under-right-multiplication-subset-Semiring R
      subset-subtractive-closure-ideal-Semiring
  is-closed-under-right-multiplication-subtractive-closure-ideal-Semiring H =
    apply-universal-property-trunc-Prop H
      ( subset-subtractive-closure-ideal-Semiring _)
      ( λ (u , u∈I , y+u∈I) →
        intro-exists
          ( mul-Semiring R u _)
          ( is-closed-under-right-multiplication-ideal-Semiring R I u∈I ,
            is-closed-under-eq-ideal-Semiring R I
              ( is-closed-under-right-multiplication-ideal-Semiring R I y+u∈I)
              ( right-distributive-mul-add-Semiring R _ _ _)))

  is-closed-under-two-sided-multiplication-subtractive-closure-ideal-Semiring :
    is-closed-under-two-sided-multiplication-subset-Semiring R
      subset-subtractive-closure-ideal-Semiring
  is-closed-under-two-sided-multiplication-subtractive-closure-ideal-Semiring
    H =
    apply-universal-property-trunc-Prop H
      ( subset-subtractive-closure-ideal-Semiring _)
      ( λ (u , u∈I , y+u∈I) →
        intro-exists
          ( mul-Semiring R (mul-Semiring R _ u) _)
          ( is-closed-under-two-sided-multiplication-ideal-Semiring R I u∈I ,
            is-closed-under-eq-ideal-Semiring R I
              ( is-closed-under-two-sided-multiplication-ideal-Semiring R I
                y+u∈I)
              ( ap
                  ( mul-Semiring' R _)
                  ( left-distributive-mul-add-Semiring R _ _ _) ∙
                right-distributive-mul-add-Semiring R _ _ _)))

  is-ideal-subtractive-closure-ideal-Semiring :
    is-ideal-subset-Semiring R subset-subtractive-closure-ideal-Semiring
  pr1 is-ideal-subtractive-closure-ideal-Semiring =
    is-additive-submonoid-subtractive-closure-ideal-Semiring
  pr2 is-ideal-subtractive-closure-ideal-Semiring =
    is-closed-under-two-sided-multiplication-subtractive-closure-ideal-Semiring

  ideal-subtractive-closure-ideal-Semiring :
    ideal-Semiring (l1 ⊔ l2) R
  pr1 ideal-subtractive-closure-ideal-Semiring =
    subset-subtractive-closure-ideal-Semiring
  pr2 ideal-subtractive-closure-ideal-Semiring =
    is-ideal-subtractive-closure-ideal-Semiring

  is-subtractive-subtractive-closure-ideal-Semiring :
    is-subtractive-ideal-Semiring R ideal-subtractive-closure-ideal-Semiring
  is-subtractive-subtractive-closure-ideal-Semiring H K =
    apply-twice-universal-property-trunc-Prop H K
      ( subset-subtractive-closure-ideal-Semiring _)
      ( λ (u , u∈I , x+u∈I) (v , v∈I , x+y+v∈I) →
        intro-exists
          ( add-Semiring R _ (add-Semiring R v u))
          ( is-closed-under-eq-ideal-Semiring R I
              ( is-closed-under-addition-ideal-Semiring R I v∈I x+u∈I)
              ( left-swap-add-Semiring R) ,
            is-closed-under-eq-ideal-Semiring' R I
              ( is-closed-under-addition-ideal-Semiring R I x+y+v∈I u∈I)
              ( left-swap-add-Semiring R ∙
                inv (associative-add-Semiring R _ _ _) ∙
                inv (associative-add-Semiring R _ _ _))))

  subtractive-closure-ideal-Semiring :
    subtractive-ideal-Semiring (l1 ⊔ l2) R
  pr1 subtractive-closure-ideal-Semiring =
    ideal-subtractive-closure-ideal-Semiring
  pr2 subtractive-closure-ideal-Semiring =
    is-subtractive-subtractive-closure-ideal-Semiring

  forward-implication-is-subtractive-closure-subtractive-closure-ideal-Semiring :
    {l3 : Level} (J : subtractive-ideal-Semiring l3 R) →
    leq-subtractive-ideal-Semiring R subtractive-closure-ideal-Semiring J →
    leq-ideal-Semiring R I (ideal-subtractive-ideal-Semiring R J)
  forward-implication-is-subtractive-closure-subtractive-closure-ideal-Semiring
    J H =
    transitive-leq-subtype
      ( subset-ideal-Semiring R I)
      ( subset-subtractive-closure-ideal-Semiring)
      ( subset-subtractive-ideal-Semiring R J)
      ( H)
      ( contains-ideal-subtractive-closure-ideal-Semiring)

  leq-subtractive-closure-ideal-Semiring :
    {l3 : Level} (J : subtractive-ideal-Semiring l3 R) →
    leq-ideal-Semiring R I (ideal-subtractive-ideal-Semiring R J) →
    leq-subtractive-ideal-Semiring R subtractive-closure-ideal-Semiring J
  leq-subtractive-closure-ideal-Semiring
    J H x K =
    apply-universal-property-trunc-Prop K
      ( subset-subtractive-ideal-Semiring R J x)
      ( λ (u , u∈I , x+u∈I) →
        is-subtractive-subtractive-ideal-Semiring R J
          ( H u u∈I)
          ( is-closed-under-eq-subtractive-ideal-Semiring R J
            ( H (add-Semiring R x u) x+u∈I)
            ( commutative-add-Semiring R _ _)))

  is-subtractive-closure-subtractive-closure-ideal-Semiring :
    is-subtractive-closure-ideal-Semiring R I subtractive-closure-ideal-Semiring
  pr1 (is-subtractive-closure-subtractive-closure-ideal-Semiring J) =
    forward-implication-is-subtractive-closure-subtractive-closure-ideal-Semiring
      J
  pr2 (is-subtractive-closure-subtractive-closure-ideal-Semiring J) =
    leq-subtractive-closure-ideal-Semiring
      J
```

#### Subtractive closure is order preserving

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  preserves-order-subtractive-closure-ideal-Semiring :
    {l2 l3 : Level} (I : ideal-Semiring l2 R) (J : ideal-Semiring l3 R) →
    leq-ideal-Semiring R I J →
    leq-subtractive-ideal-Semiring R
      ( subtractive-closure-ideal-Semiring R I)
      ( subtractive-closure-ideal-Semiring R J)
  preserves-order-subtractive-closure-ideal-Semiring I J H =
    leq-subtractive-closure-ideal-Semiring R I
      ( subtractive-closure-ideal-Semiring R J)
      ( transitive-leq-ideal-Semiring R I J
        ( ideal-subtractive-closure-ideal-Semiring R J)
        ( contains-ideal-subtractive-closure-ideal-Semiring R J)
        ( H))

  subtractive-closure-ideal-hom-large-poset-Semiring :
    hom-Large-Poset
      ( λ l2 → l1 ⊔ l2)
      ( ideal-Semiring-Large-Poset R)
      ( subtractive-ideal-Semiring-Large-Poset R)
  map-hom-Large-Preorder
    subtractive-closure-ideal-hom-large-poset-Semiring =
    subtractive-closure-ideal-Semiring R
  preserves-order-hom-Large-Preorder
    subtractive-closure-ideal-hom-large-poset-Semiring =
    preserves-order-subtractive-closure-ideal-Semiring
```

#### The subtractive closure Galois connection

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  adjoint-relation-subtractive-closure-ideal-Semiring :
    {l2 l3 : Level}
    (I : ideal-Semiring l2 R) (J : subtractive-ideal-Semiring l3 R) →
    leq-subtractive-ideal-Semiring R
      ( subtractive-closure-ideal-Semiring R I)
      ( J) ↔
    leq-ideal-Semiring R I (ideal-subtractive-ideal-Semiring R J)
  adjoint-relation-subtractive-closure-ideal-Semiring I J =
    is-subtractive-closure-subtractive-closure-ideal-Semiring R I J

  subtractive-closure-ideal-galois-connection-Semiring :
    galois-connection-Large-Poset
      ( λ l2 → l1 ⊔ l2)
      ( λ l → l)
      ( ideal-Semiring-Large-Poset R)
      ( subtractive-ideal-Semiring-Large-Poset R)
  lower-adjoint-galois-connection-Large-Poset
    subtractive-closure-ideal-galois-connection-Semiring =
    subtractive-closure-ideal-hom-large-poset-Semiring R
  upper-adjoint-galois-connection-Large-Poset
    subtractive-closure-ideal-galois-connection-Semiring =
    ideal-subtractive-ideal-hom-large-poset-Semiring R
  adjoint-relation-galois-connection-Large-Poset
    subtractive-closure-ideal-galois-connection-Semiring =
    adjoint-relation-subtractive-closure-ideal-Semiring
```

#### The subtractive closure reflective Galois connection

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  forward-inclusion-is-reflective-subtractive-closure-ideal-Semiring :
    {l2 : Level} (I : subtractive-ideal-Semiring l2 R) →
    leq-subtractive-ideal-Semiring R
      ( subtractive-closure-ideal-Semiring R
        ( ideal-subtractive-ideal-Semiring R I))
      ( I)
  forward-inclusion-is-reflective-subtractive-closure-ideal-Semiring I =
    leq-subtractive-closure-ideal-Semiring R
      ( ideal-subtractive-ideal-Semiring R I)
      ( I)
      ( refl-leq-subtractive-ideal-Semiring R I)

  backward-inclusion-is-reflective-subtractive-closure-ideal-Semiring :
    {l2 : Level} (I : subtractive-ideal-Semiring l2 R) →
    leq-subtractive-ideal-Semiring R I
      ( subtractive-closure-ideal-Semiring R
        ( ideal-subtractive-ideal-Semiring R I))
  backward-inclusion-is-reflective-subtractive-closure-ideal-Semiring I =
    contains-ideal-subtractive-closure-ideal-Semiring R
      ( ideal-subtractive-ideal-Semiring R I)

  is-reflective-subtractive-closure-ideal-Semiring :
    is-reflective-galois-connection-Large-Poset
      ( ideal-Semiring-Large-Poset R)
      ( subtractive-ideal-Semiring-Large-Poset R)
      ( subtractive-closure-ideal-galois-connection-Semiring R)
  pr1 (is-reflective-subtractive-closure-ideal-Semiring I) =
    forward-inclusion-is-reflective-subtractive-closure-ideal-Semiring I
  pr2 (is-reflective-subtractive-closure-ideal-Semiring I) =
    backward-inclusion-is-reflective-subtractive-closure-ideal-Semiring I

  subtractive-closure-ideal-reflective-galois-connection-Semiring :
    reflective-galois-connection-Large-Poset
      ( ideal-Semiring-Large-Poset R)
      ( subtractive-ideal-Semiring-Large-Poset R)
  galois-connection-reflective-galois-connection-Large-Poset
    subtractive-closure-ideal-reflective-galois-connection-Semiring =
    subtractive-closure-ideal-galois-connection-Semiring R
  is-reflective-reflective-galois-connection-Large-Poset
    subtractive-closure-ideal-reflective-galois-connection-Semiring =
    is-reflective-subtractive-closure-ideal-Semiring
```

### The subtractive ideal generated by a family of ideals of a semiring

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) {U : UU l2} (I : U → ideal-Semiring l3 R)
  where

  generating-ideal-subtractive-ideal-family-of-ideals-Semiring :
    ideal-Semiring (l1 ⊔ l2 ⊔ l3) R
  generating-ideal-subtractive-ideal-family-of-ideals-Semiring =
    join-family-of-ideals-Semiring R I

  subtractive-ideal-family-of-ideals-Semiring :
    subtractive-ideal-Semiring (l1 ⊔ l2 ⊔ l3) R
  subtractive-ideal-family-of-ideals-Semiring =
    subtractive-closure-ideal-Semiring R
      generating-ideal-subtractive-ideal-family-of-ideals-Semiring

  ideal-subtractive-ideal-family-of-ideals-Semiring :
    ideal-Semiring (l1 ⊔ l2 ⊔ l3) R
  ideal-subtractive-ideal-family-of-ideals-Semiring =
    ideal-subtractive-closure-ideal-Semiring R
      generating-ideal-subtractive-ideal-family-of-ideals-Semiring

  is-in-subtractive-ideal-family-of-ideals-Semiring :
    type-Semiring R → UU (l1 ⊔ l2 ⊔ l3)
  is-in-subtractive-ideal-family-of-ideals-Semiring =
    is-in-subtractive-closure-ideal-Semiring R
      generating-ideal-subtractive-ideal-family-of-ideals-Semiring

  contains-ideal-subtractive-ideal-family-of-ideals-Semiring :
    {α : U} →
    leq-ideal-Semiring R (I α) ideal-subtractive-ideal-family-of-ideals-Semiring
  contains-ideal-subtractive-ideal-family-of-ideals-Semiring {α} =
    transitive-leq-ideal-Semiring R
      ( I α)
      ( generating-ideal-subtractive-ideal-family-of-ideals-Semiring)
      ( ideal-subtractive-ideal-family-of-ideals-Semiring)
      ( contains-ideal-subtractive-closure-ideal-Semiring R
        generating-ideal-subtractive-ideal-family-of-ideals-Semiring)
      ( contains-ideal-join-family-of-ideals-Semiring R I)

  is-subtractive-ideal-generated-by-family-of-ideals-subtractive-ideal-family-of-ideals-Semiring :
    is-subtractive-ideal-generated-by-family-of-ideals-Semiring R I
      ( subtractive-ideal-family-of-ideals-Semiring)
      ( λ α → contains-ideal-subtractive-ideal-family-of-ideals-Semiring)
  is-subtractive-ideal-generated-by-family-of-ideals-subtractive-ideal-family-of-ideals-Semiring
    J H =
    leq-subtractive-closure-ideal-Semiring R
      ( generating-ideal-subtractive-ideal-family-of-ideals-Semiring)
      ( J)
      ( leq-join-family-of-ideals-Semiring R I
        ( ideal-subtractive-ideal-Semiring R J)
        ( H))
```

## Properties

### The subtractive ideal generated by the underlying ideal of a subtractive ideal `I` is `I` itself

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : subtractive-ideal-Semiring l2 R)
  where

  idempotent-subtractive-closure-ideal-Semiring :
    has-same-elements-subtractive-ideal-Semiring R
      ( subtractive-closure-ideal-Semiring R
        ( ideal-subtractive-ideal-Semiring R I))
      ( I)
  idempotent-subtractive-closure-ideal-Semiring =
    has-same-elements-sim-subtype
      ( subset-subtractive-closure-ideal-Semiring R
        ( ideal-subtractive-ideal-Semiring R I))
      ( subset-subtractive-ideal-Semiring R I)
      ( is-reflective-subtractive-closure-ideal-Semiring R I)
```

### Subtractive closure preserves least upper bounds

In
[`ring-theory.joins-subtractive-ideals-semirings`](ring-theory.joins-subtractive-ideals-semirings.md)
we will convert this fact to the fact that subtractive closure preserves joins.

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {U : UU l2} (I : U → ideal-Semiring l3 R)
  where

  preserves-least-upper-bounds-subtractive-closure-ideal-Semiring :
    {l4 : Level} (J : ideal-Semiring l4 R) →
    is-join-family-of-ideals-Semiring R
      ( I)
      ( J) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( subtractive-ideal-Semiring-Large-Poset R)
      ( λ α → subtractive-closure-ideal-Semiring R (I α))
      ( subtractive-closure-ideal-Semiring R J)
  preserves-least-upper-bounds-subtractive-closure-ideal-Semiring =
    preserves-join-lower-adjoint-galois-connection-Large-Poset
      ( ideal-Semiring-Large-Poset R)
      ( subtractive-ideal-Semiring-Large-Poset R)
      ( subtractive-closure-ideal-galois-connection-Semiring R)
      ( I)
```
