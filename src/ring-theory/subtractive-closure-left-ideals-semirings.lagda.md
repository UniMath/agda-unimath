# The subtractive closure of left ideals of semirings

```agda
module ring-theory.subtractive-closure-left-ideals-semirings where
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

open import ring-theory.left-ideals-semirings
open import ring-theory.joins-left-ideals-semirings
open import ring-theory.poset-of-left-ideals-semirings
open import ring-theory.poset-of-subtractive-left-ideals-semirings
open import ring-theory.semirings
open import ring-theory.subsets-semirings
open import ring-theory.subtractive-left-ideals-semirings
```

</details>

## Idea

The {{#concept "subtractive closure" Disambiguation="left ideal of a semiring" Agda=subtractive-closure-left-ideal-Semiring}} of a [left ideal](ring-theory.left-ideals-semirings.md) `I` of a [semiring](ring-theory.semirings.md) `R` is the least [subtractive left ideal](ring-theory.subtractive-left-ideals-semirings.lagda.md) containing `I`. More concretely, the subtractive closure `S(I)` consists of those elements `x : R` for which there [exists](foundation.existential-quantification.md) an `y ∈ I` such that `x + y ∈ I`.

**Theorem** Consider a left ideal `I` of `R`. Then the set `S(I)` consisting of `x : R` for which there exists an element `y ∈ I` such that `x + y ∈ I` is a subtractive left ideal.

*Proof.*
- Note that `0 ∈ S(I)` since `0 ∈ I` and `0 + 0 ∈ I`.
- If `x y ∈ S(I)` with `u v ∈ I` such that `x + u ∈ I` and `y + v ∈ I`, then `u + v ∈ I` and `(x + y) + (u + v) = (x + u) + (y + v) ∈ I`.
- If `x z : R` and `y ∈ S(I)` with `u ∈ I` such that `y + u ∈ I`, then we have `(xu)z ∈ I` and `(x(y+u))z = (xy)z + (xu)z ∈ I`.
- If `x (x + y) ∈ S(I)` with `u v ∈ I` such that `x + u ∈ I` and `(x + y) + v ∈ I`, then we have `x + (v + u) ∈ I` and `y + (x + (v + u)) = ((x + y) + v) + u ∈ I`.

The universal property of the subtractive closure `S(I)` of `I` states that for any subtractive left ideal `J` we have the following [logical equivalence](foundation.logical-equivalences.md):

```text
  S(I) ⊆ J ⇔ I ⊆ J.
```

Thus, there is a [large Galois connection](order-theory.galois-connections.md) between the [large poset](order-theory.large-posets.md) of left ideals of `R` and the poset of subtractive left ideals of `R`.

## Definitions

### The universal property of the subtractive closure

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  (I : left-ideal-Semiring l2 R) (I' : subtractive-left-ideal-Semiring l3 R)
  where

  is-subtractive-closure-left-ideal-Semiring : UUω
  is-subtractive-closure-left-ideal-Semiring =
    {l4 : Level} (J : subtractive-left-ideal-Semiring l4 R) →
    leq-subtractive-left-ideal-Semiring R I' J ↔
    leq-left-ideal-Semiring R I (left-ideal-subtractive-left-ideal-Semiring R J)

  contains-left-ideal-is-subtractive-closure-left-ideal-Semiring :
    is-subtractive-closure-left-ideal-Semiring →
    leq-left-ideal-Semiring R I
      ( left-ideal-subtractive-left-ideal-Semiring R I')
  contains-left-ideal-is-subtractive-closure-left-ideal-Semiring U =
    forward-implication (U I') (refl-leq-subtractive-left-ideal-Semiring R I')

  leq-is-subtractive-closure-left-ideal-Semiring :
    is-subtractive-closure-left-ideal-Semiring →
    {l4 : Level} (J : subtractive-left-ideal-Semiring l4 R) →
    leq-left-ideal-Semiring R I
      ( left-ideal-subtractive-left-ideal-Semiring R J) →
    leq-subtractive-left-ideal-Semiring R I' J
  leq-is-subtractive-closure-left-ideal-Semiring U J =
    backward-implication (U J)
```

### The universal property of the subtractive closure of a family of left ideals of a semiring

```agda
module _
  {l1 l2 l3 l4 : Level} (R : Semiring l1) {U : UU l2}
  (I : U → left-ideal-Semiring l3 R)
  (J : subtractive-left-ideal-Semiring l4 R)
  (H :
    (α : U) →
    leq-left-ideal-Semiring R
      ( I α)
      ( left-ideal-subtractive-left-ideal-Semiring R J))
  where

  is-subtractive-left-ideal-generated-by-family-of-left-ideals-Semiring : UUω
  is-subtractive-left-ideal-generated-by-family-of-left-ideals-Semiring =
    {l : Level} (K : subtractive-left-ideal-Semiring l R) →
    ( (α : U) →
      leq-left-ideal-Semiring R
        ( I α)
        ( left-ideal-subtractive-left-ideal-Semiring R K)) →
    leq-subtractive-left-ideal-Semiring R J K
```


### Construction of the subtractive closure Galois connection

#### The subtractive closure of an ideal

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : left-ideal-Semiring l2 R)
  where

  subset-subtractive-closure-left-ideal-Semiring :
    subset-Semiring (l1 ⊔ l2) R
  subset-subtractive-closure-left-ideal-Semiring x =
    ∃ ( type-Semiring R)
      ( λ y →
        subset-left-ideal-Semiring R I y ∧
        subset-left-ideal-Semiring R I (add-Semiring R x y))

  is-in-subtractive-closure-left-ideal-Semiring : type-Semiring R → UU (l1 ⊔ l2)
  is-in-subtractive-closure-left-ideal-Semiring =
    is-in-subset-Semiring R subset-subtractive-closure-left-ideal-Semiring

  is-prop-is-in-subtractive-closure-left-ideal-Semiring :
    (x : type-Semiring R) →
    is-prop (is-in-subtractive-closure-left-ideal-Semiring x)
  is-prop-is-in-subtractive-closure-left-ideal-Semiring =
    is-prop-is-in-subset-Semiring R
      subset-subtractive-closure-left-ideal-Semiring

  type-subtractive-closure-left-ideal-Semiring : UU (l1 ⊔ l2)
  type-subtractive-closure-left-ideal-Semiring =
    type-subset-Semiring R subset-subtractive-closure-left-ideal-Semiring

  inclusion-subtractive-closure-left-ideal-Semiring :
    type-subtractive-closure-left-ideal-Semiring → type-Semiring R
  inclusion-subtractive-closure-left-ideal-Semiring =
    inclusion-subset-Semiring R subset-subtractive-closure-left-ideal-Semiring

  ap-inclusion-subtractive-closure-left-ideal-Semiring :
    (x y : type-subtractive-closure-left-ideal-Semiring) → x ＝ y →
    inclusion-subtractive-closure-left-ideal-Semiring x ＝
    inclusion-subtractive-closure-left-ideal-Semiring y
  ap-inclusion-subtractive-closure-left-ideal-Semiring =
    ap-inclusion-subset-Semiring R
      subset-subtractive-closure-left-ideal-Semiring

  is-in-subset-inclusion-subtractive-closure-left-ideal-Semiring :
    (x : type-subtractive-closure-left-ideal-Semiring) →
    is-in-subtractive-closure-left-ideal-Semiring
      ( inclusion-subtractive-closure-left-ideal-Semiring x)
  is-in-subset-inclusion-subtractive-closure-left-ideal-Semiring =
    is-in-subset-inclusion-subset-Semiring R
      subset-subtractive-closure-left-ideal-Semiring

  is-closed-under-eq-subtractive-closure-left-ideal-Semiring :
    {x y : type-Semiring R} → is-in-subtractive-closure-left-ideal-Semiring x →
    (x ＝ y) → is-in-subtractive-closure-left-ideal-Semiring y
  is-closed-under-eq-subtractive-closure-left-ideal-Semiring =
    is-closed-under-eq-subset-Semiring R
      subset-subtractive-closure-left-ideal-Semiring

  is-closed-under-eq-subtractive-closure-left-ideal-Semiring' :
    {x y : type-Semiring R} → is-in-subtractive-closure-left-ideal-Semiring y →
    (x ＝ y) → is-in-subtractive-closure-left-ideal-Semiring x
  is-closed-under-eq-subtractive-closure-left-ideal-Semiring' =
    is-closed-under-eq-subset-Semiring' R
      subset-subtractive-closure-left-ideal-Semiring

  contains-left-ideal-subtractive-closure-left-ideal-Semiring :
    subset-left-ideal-Semiring R I ⊆
    subset-subtractive-closure-left-ideal-Semiring
  contains-left-ideal-subtractive-closure-left-ideal-Semiring x H =
    intro-exists
      ( zero-Semiring R)
      ( contains-zero-left-ideal-Semiring R I ,
        is-closed-under-addition-left-ideal-Semiring R I H
          ( contains-zero-left-ideal-Semiring R I))

  contains-zero-subtractive-closure-left-ideal-Semiring :
    is-in-subtractive-closure-left-ideal-Semiring (zero-Semiring R)
  contains-zero-subtractive-closure-left-ideal-Semiring =
    contains-left-ideal-subtractive-closure-left-ideal-Semiring _
      ( contains-zero-left-ideal-Semiring R I)

  is-closed-under-addition-subtractive-closure-left-ideal-Semiring :
    {x y : type-Semiring R} →
    is-in-subtractive-closure-left-ideal-Semiring x →
    is-in-subtractive-closure-left-ideal-Semiring y →
    is-in-subtractive-closure-left-ideal-Semiring (add-Semiring R x y)
  is-closed-under-addition-subtractive-closure-left-ideal-Semiring H K =
    apply-twice-universal-property-trunc-Prop H K
      ( subset-subtractive-closure-left-ideal-Semiring (add-Semiring R _ _))
      ( λ (u , u∈I , x+u∈I) (v , v∈I , y+v∈I) →
        intro-exists
          ( add-Semiring R u v)
          ( is-closed-under-addition-left-ideal-Semiring R I u∈I v∈I ,
            is-closed-under-eq-left-ideal-Semiring R I
              ( is-closed-under-addition-left-ideal-Semiring R I x+u∈I y+v∈I)
              ( interchange-add-add-Semiring R)))

  is-additive-submonoid-subtractive-closure-left-ideal-Semiring :
    is-additive-submonoid-subset-Semiring R
      subset-subtractive-closure-left-ideal-Semiring
  pr1 is-additive-submonoid-subtractive-closure-left-ideal-Semiring =
    contains-zero-subtractive-closure-left-ideal-Semiring
  pr2 is-additive-submonoid-subtractive-closure-left-ideal-Semiring =
    is-closed-under-addition-subtractive-closure-left-ideal-Semiring

  additive-submonoid-subtractive-closure-left-ideal-Semiring :
    Submonoid (l1 ⊔ l2) (additive-monoid-Semiring R)
  pr1 additive-submonoid-subtractive-closure-left-ideal-Semiring =
    subset-subtractive-closure-left-ideal-Semiring
  pr2 additive-submonoid-subtractive-closure-left-ideal-Semiring =
    is-additive-submonoid-subtractive-closure-left-ideal-Semiring

  is-closed-under-left-multiplication-subtractive-closure-left-ideal-Semiring :
    is-closed-under-left-multiplication-subset-Semiring R
      subset-subtractive-closure-left-ideal-Semiring
  is-closed-under-left-multiplication-subtractive-closure-left-ideal-Semiring
    H =
    apply-universal-property-trunc-Prop H
      ( subset-subtractive-closure-left-ideal-Semiring _)
      ( λ (u , u∈I , y+u∈I) →
        intro-exists
          ( mul-Semiring R _ u)
          ( is-closed-under-left-multiplication-left-ideal-Semiring R I u∈I ,
            is-closed-under-eq-left-ideal-Semiring R I
              ( is-closed-under-left-multiplication-left-ideal-Semiring R I
                y+u∈I)
              ( left-distributive-mul-add-Semiring R _ _ _)))

  is-left-ideal-subtractive-closure-left-ideal-Semiring :
    is-left-ideal-subset-Semiring R
      subset-subtractive-closure-left-ideal-Semiring
  pr1 is-left-ideal-subtractive-closure-left-ideal-Semiring =
    is-additive-submonoid-subtractive-closure-left-ideal-Semiring
  pr2 is-left-ideal-subtractive-closure-left-ideal-Semiring =
    is-closed-under-left-multiplication-subtractive-closure-left-ideal-Semiring

  left-ideal-subtractive-closure-left-ideal-Semiring :
    left-ideal-Semiring (l1 ⊔ l2) R
  pr1 left-ideal-subtractive-closure-left-ideal-Semiring =
    subset-subtractive-closure-left-ideal-Semiring
  pr2 left-ideal-subtractive-closure-left-ideal-Semiring =
    is-left-ideal-subtractive-closure-left-ideal-Semiring

  is-subtractive-subtractive-closure-left-ideal-Semiring :
    is-subtractive-left-ideal-Semiring R
      left-ideal-subtractive-closure-left-ideal-Semiring
  is-subtractive-subtractive-closure-left-ideal-Semiring H K =
    apply-twice-universal-property-trunc-Prop H K
      ( subset-subtractive-closure-left-ideal-Semiring _)
      ( λ (u , u∈I , x+u∈I) (v , v∈I , x+y+v∈I) →
        intro-exists
          ( add-Semiring R _ (add-Semiring R v u))
          ( is-closed-under-eq-left-ideal-Semiring R I
              ( is-closed-under-addition-left-ideal-Semiring R I v∈I x+u∈I)
              ( left-swap-add-Semiring R) ,
            is-closed-under-eq-left-ideal-Semiring' R I
              ( is-closed-under-addition-left-ideal-Semiring R I x+y+v∈I u∈I)
              ( left-swap-add-Semiring R ∙
                inv (associative-add-Semiring R _ _ _) ∙
                inv (associative-add-Semiring R _ _ _))))

  subtractive-closure-left-ideal-Semiring :
    subtractive-left-ideal-Semiring (l1 ⊔ l2) R
  pr1 subtractive-closure-left-ideal-Semiring =
    left-ideal-subtractive-closure-left-ideal-Semiring
  pr2 subtractive-closure-left-ideal-Semiring =
    is-subtractive-subtractive-closure-left-ideal-Semiring

  forward-implication-is-subtractive-closure-subtractive-closure-left-ideal-Semiring :
    {l3 : Level} (J : subtractive-left-ideal-Semiring l3 R) →
    leq-subtractive-left-ideal-Semiring R
      subtractive-closure-left-ideal-Semiring J →
    leq-left-ideal-Semiring R I (left-ideal-subtractive-left-ideal-Semiring R J)
  forward-implication-is-subtractive-closure-subtractive-closure-left-ideal-Semiring
    J H =
    transitive-leq-subtype
      ( subset-left-ideal-Semiring R I)
      ( subset-subtractive-closure-left-ideal-Semiring)
      ( subset-subtractive-left-ideal-Semiring R J)
      ( H)
      ( contains-left-ideal-subtractive-closure-left-ideal-Semiring)

  leq-subtractive-closure-left-ideal-Semiring :
    {l3 : Level} (J : subtractive-left-ideal-Semiring l3 R) →
    leq-left-ideal-Semiring R I
      ( left-ideal-subtractive-left-ideal-Semiring R J) →
    leq-subtractive-left-ideal-Semiring R
      subtractive-closure-left-ideal-Semiring J
  leq-subtractive-closure-left-ideal-Semiring
    J H x K =
    apply-universal-property-trunc-Prop K
      ( subset-subtractive-left-ideal-Semiring R J x)
      ( λ (u , u∈I , x+u∈I) →
        is-subtractive-subtractive-left-ideal-Semiring R J
          ( H u u∈I)
          ( is-closed-under-eq-subtractive-left-ideal-Semiring R J
            ( H (add-Semiring R x u) x+u∈I)
            ( commutative-add-Semiring R _ _)))

  is-subtractive-closure-subtractive-closure-left-ideal-Semiring :
    is-subtractive-closure-left-ideal-Semiring R I
      subtractive-closure-left-ideal-Semiring
  pr1 (is-subtractive-closure-subtractive-closure-left-ideal-Semiring J) =
    forward-implication-is-subtractive-closure-subtractive-closure-left-ideal-Semiring
      J
  pr2 (is-subtractive-closure-subtractive-closure-left-ideal-Semiring J) =
    leq-subtractive-closure-left-ideal-Semiring
      J
```

#### Subtractive closure is order preserving

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  preserves-order-subtractive-closure-left-ideal-Semiring :
    {l2 l3 : Level}
    (I : left-ideal-Semiring l2 R) (J : left-ideal-Semiring l3 R) →
    leq-left-ideal-Semiring R I J →
    leq-subtractive-left-ideal-Semiring R
      ( subtractive-closure-left-ideal-Semiring R I)
      ( subtractive-closure-left-ideal-Semiring R J)
  preserves-order-subtractive-closure-left-ideal-Semiring I J H =
    leq-subtractive-closure-left-ideal-Semiring R I
      ( subtractive-closure-left-ideal-Semiring R J)
      ( transitive-leq-left-ideal-Semiring R I J
        ( left-ideal-subtractive-closure-left-ideal-Semiring R J)
        ( contains-left-ideal-subtractive-closure-left-ideal-Semiring R J)
        ( H))

  subtractive-closure-left-ideal-hom-large-poset-Semiring :
    hom-Large-Poset
      ( λ l2 → l1 ⊔ l2)
      ( left-ideal-Semiring-Large-Poset R)
      ( subtractive-left-ideal-Semiring-Large-Poset R)
  map-hom-Large-Preorder
    subtractive-closure-left-ideal-hom-large-poset-Semiring =
    subtractive-closure-left-ideal-Semiring R
  preserves-order-hom-Large-Preorder
    subtractive-closure-left-ideal-hom-large-poset-Semiring =
    preserves-order-subtractive-closure-left-ideal-Semiring
```

#### The subtractive closure Galois connection

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  adjoint-relation-subtractive-closure-left-ideal-Semiring :
    {l2 l3 : Level}
    (I : left-ideal-Semiring l2 R) (J : subtractive-left-ideal-Semiring l3 R) →
    leq-subtractive-left-ideal-Semiring R
      ( subtractive-closure-left-ideal-Semiring R I)
      ( J) ↔
    leq-left-ideal-Semiring R I (left-ideal-subtractive-left-ideal-Semiring R J)
  adjoint-relation-subtractive-closure-left-ideal-Semiring I J =
    is-subtractive-closure-subtractive-closure-left-ideal-Semiring R I J

  subtractive-closure-left-ideal-galois-connection-Semiring :
    galois-connection-Large-Poset
      ( λ l2 → l1 ⊔ l2)
      ( λ l → l)
      ( left-ideal-Semiring-Large-Poset R)
      ( subtractive-left-ideal-Semiring-Large-Poset R)
  lower-adjoint-galois-connection-Large-Poset
    subtractive-closure-left-ideal-galois-connection-Semiring =
    subtractive-closure-left-ideal-hom-large-poset-Semiring R
  upper-adjoint-galois-connection-Large-Poset
    subtractive-closure-left-ideal-galois-connection-Semiring =
    left-ideal-subtractive-left-ideal-hom-large-poset-Semiring R
  adjoint-relation-galois-connection-Large-Poset
    subtractive-closure-left-ideal-galois-connection-Semiring =
    adjoint-relation-subtractive-closure-left-ideal-Semiring
```

#### The subtractive closure reflective Galois connection

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  forward-inclusion-is-reflective-subtractive-closure-left-ideal-Semiring :
    {l2 : Level} (I : subtractive-left-ideal-Semiring l2 R) →
    leq-subtractive-left-ideal-Semiring R
      ( subtractive-closure-left-ideal-Semiring R
        ( left-ideal-subtractive-left-ideal-Semiring R I))
      ( I)
  forward-inclusion-is-reflective-subtractive-closure-left-ideal-Semiring I =
    leq-subtractive-closure-left-ideal-Semiring R
      ( left-ideal-subtractive-left-ideal-Semiring R I)
      ( I)
      ( refl-leq-subtractive-left-ideal-Semiring R I)

  backward-inclusion-is-reflective-subtractive-closure-left-ideal-Semiring :
    {l2 : Level} (I : subtractive-left-ideal-Semiring l2 R) →
    leq-subtractive-left-ideal-Semiring R I
      ( subtractive-closure-left-ideal-Semiring R
        ( left-ideal-subtractive-left-ideal-Semiring R I))
  backward-inclusion-is-reflective-subtractive-closure-left-ideal-Semiring I =
    contains-left-ideal-subtractive-closure-left-ideal-Semiring R
      ( left-ideal-subtractive-left-ideal-Semiring R I)

  is-reflective-subtractive-closure-left-ideal-Semiring :
    is-reflective-galois-connection-Large-Poset
      ( left-ideal-Semiring-Large-Poset R)
      ( subtractive-left-ideal-Semiring-Large-Poset R)
      ( subtractive-closure-left-ideal-galois-connection-Semiring R)
  pr1 (is-reflective-subtractive-closure-left-ideal-Semiring I) =
    forward-inclusion-is-reflective-subtractive-closure-left-ideal-Semiring I
  pr2 (is-reflective-subtractive-closure-left-ideal-Semiring I) =
    backward-inclusion-is-reflective-subtractive-closure-left-ideal-Semiring I

  subtractive-closure-left-ideal-reflective-galois-connection-Semiring :
    reflective-galois-connection-Large-Poset
      ( left-ideal-Semiring-Large-Poset R)
      ( subtractive-left-ideal-Semiring-Large-Poset R)
  galois-connection-reflective-galois-connection-Large-Poset
    subtractive-closure-left-ideal-reflective-galois-connection-Semiring =
    subtractive-closure-left-ideal-galois-connection-Semiring R
  is-reflective-reflective-galois-connection-Large-Poset
    subtractive-closure-left-ideal-reflective-galois-connection-Semiring =
    is-reflective-subtractive-closure-left-ideal-Semiring
```

### The subtractive left ideal generated by a family of left ideals of a semiring

```agda
module _
  {l1 l2 l3 : Level}
  (R : Semiring l1) {U : UU l2} (I : U → left-ideal-Semiring l3 R)
  where

  generating-left-ideal-subtractive-left-ideal-family-of-left-ideals-Semiring :
    left-ideal-Semiring (l1 ⊔ l2 ⊔ l3) R
  generating-left-ideal-subtractive-left-ideal-family-of-left-ideals-Semiring =
    join-family-of-left-ideals-Semiring R I

  subtractive-left-ideal-family-of-left-ideals-Semiring :
    subtractive-left-ideal-Semiring (l1 ⊔ l2 ⊔ l3) R
  subtractive-left-ideal-family-of-left-ideals-Semiring =
    subtractive-closure-left-ideal-Semiring R
      generating-left-ideal-subtractive-left-ideal-family-of-left-ideals-Semiring

  left-ideal-subtractive-left-ideal-family-of-left-ideals-Semiring :
    left-ideal-Semiring (l1 ⊔ l2 ⊔ l3) R
  left-ideal-subtractive-left-ideal-family-of-left-ideals-Semiring =
    left-ideal-subtractive-closure-left-ideal-Semiring R
      generating-left-ideal-subtractive-left-ideal-family-of-left-ideals-Semiring

  is-in-subtractive-left-ideal-family-of-left-ideals-Semiring :
    type-Semiring R → UU (l1 ⊔ l2 ⊔ l3)
  is-in-subtractive-left-ideal-family-of-left-ideals-Semiring =
    is-in-subtractive-closure-left-ideal-Semiring R
      generating-left-ideal-subtractive-left-ideal-family-of-left-ideals-Semiring

  contains-left-ideal-subtractive-left-ideal-family-of-left-ideals-Semiring :
    {α : U} →
    leq-left-ideal-Semiring R
      ( I α)
      ( left-ideal-subtractive-left-ideal-family-of-left-ideals-Semiring)
  contains-left-ideal-subtractive-left-ideal-family-of-left-ideals-Semiring =
    transitive-leq-left-ideal-Semiring R
      ( I _)
      ( generating-left-ideal-subtractive-left-ideal-family-of-left-ideals-Semiring)
      ( left-ideal-subtractive-left-ideal-family-of-left-ideals-Semiring)
      ( contains-left-ideal-subtractive-closure-left-ideal-Semiring R
        generating-left-ideal-subtractive-left-ideal-family-of-left-ideals-Semiring)
      ( contains-left-ideal-join-family-of-left-ideals-Semiring R I)

  is-subtractive-left-ideal-generated-by-family-of-left-ideals-subtractive-left-ideal-family-of-left-ideals-Semiring :
    is-subtractive-left-ideal-generated-by-family-of-left-ideals-Semiring R I
      ( subtractive-left-ideal-family-of-left-ideals-Semiring)
      ( λ α →
        contains-left-ideal-subtractive-left-ideal-family-of-left-ideals-Semiring)
  is-subtractive-left-ideal-generated-by-family-of-left-ideals-subtractive-left-ideal-family-of-left-ideals-Semiring
    J H =
    leq-subtractive-closure-left-ideal-Semiring R
      ( generating-left-ideal-subtractive-left-ideal-family-of-left-ideals-Semiring)
      ( J)
      ( leq-join-family-of-left-ideals-Semiring R I
        ( left-ideal-subtractive-left-ideal-Semiring R J)
        ( H))
```

## Properties

### The subtractive left ideal generated by the underlying left ideal of a subtractive left ideal `I` is `I` itself

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : subtractive-left-ideal-Semiring l2 R)
  where

  idempotent-subtractive-closure-left-ideal-Semiring :
    has-same-elements-subtractive-left-ideal-Semiring R
      ( subtractive-closure-left-ideal-Semiring R
        ( left-ideal-subtractive-left-ideal-Semiring R I))
      ( I)
  idempotent-subtractive-closure-left-ideal-Semiring =
    has-same-elements-sim-subtype
      ( subset-subtractive-closure-left-ideal-Semiring R
        ( left-ideal-subtractive-left-ideal-Semiring R I))
      ( subset-subtractive-left-ideal-Semiring R I)
      ( is-reflective-subtractive-closure-left-ideal-Semiring R I)
```

### Subtractive closure preserves least upper bounds

In
[`ring-theory.joins-subtractive-left-ideals-semirings`](ring-theory.joins-subtractive-left-ideals-semirings.md)
we will convert this fact to the fact that subtractive closure preserves joins.

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {U : UU l2} (I : U → left-ideal-Semiring l3 R)
  where

  preserves-least-upper-bounds-subtractive-closure-left-ideal-Semiring :
    {l4 : Level} (J : left-ideal-Semiring l4 R) →
    is-join-family-of-left-ideals-Semiring R
      ( I)
      ( J) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( subtractive-left-ideal-Semiring-Large-Poset R)
      ( λ α → subtractive-closure-left-ideal-Semiring R (I α))
      ( subtractive-closure-left-ideal-Semiring R J)
  preserves-least-upper-bounds-subtractive-closure-left-ideal-Semiring =
    preserves-join-lower-adjoint-galois-connection-Large-Poset
      ( left-ideal-Semiring-Large-Poset R)
      ( subtractive-left-ideal-Semiring-Large-Poset R)
      ( subtractive-closure-left-ideal-galois-connection-Semiring R)
      ( I)
```
