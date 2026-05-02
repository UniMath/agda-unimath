# The subtractive closure of right ideals of semirings

```agda
module ring-theory.subtractive-closure-right-ideals-semirings where
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

open import ring-theory.right-ideals-semirings
open import ring-theory.joins-right-ideals-semirings
open import ring-theory.poset-of-right-ideals-semirings
open import ring-theory.poset-of-subtractive-right-ideals-semirings
open import ring-theory.semirings
open import ring-theory.subsets-semirings
open import ring-theory.subtractive-right-ideals-semirings
```

</details>

## Idea

The {{#concept "subtractive closure" Disambiguation="right ideal of a semiring" Agda=subtractive-closure-right-ideal-Semiring}} of a [right ideal](ring-theory.right-ideals-semirings.md) `I` of a [semiring](ring-theory.semirings.md) `R` is the least [subtractive right ideal](ring-theory.subtractive-right-ideals-semirings.lagda.md) containing `I`. More concretely, the subtractive closure `S(I)` consists of those elements `x : R` for which there [exists](foundation.existential-quantification.md) an `y ∈ I` such that `x + y ∈ I`.

**Theorem** Consider a right ideal `I` of `R`. Then the set `S(I)` consisting of `x : R` for which there exists an element `y ∈ I` such that `x + y ∈ I` is a subtractive right ideal.

*Proof.*
- Note that `0 ∈ S(I)` since `0 ∈ I` and `0 + 0 ∈ I`.
- If `x y ∈ S(I)` with `u v ∈ I` such that `x + u ∈ I` and `y + v ∈ I`, then `u + v ∈ I` and `(x + y) + (u + v) = (x + u) + (y + v) ∈ I`.
- If `x z : R` and `y ∈ S(I)` with `u ∈ I` such that `y + u ∈ I`, then we have `(xu)z ∈ I` and `(x(y+u))z = (xy)z + (xu)z ∈ I`.
- If `x (x + y) ∈ S(I)` with `u v ∈ I` such that `x + u ∈ I` and `(x + y) + v ∈ I`, then we have `x + (v + u) ∈ I` and `y + (x + (v + u)) = ((x + y) + v) + u ∈ I`.

The universal property of the subtractive closure `S(I)` of `I` states that for any subtractive right ideal `J` we have the following [logical equivalence](foundation.logical-equivalences.md):

```text
  S(I) ⊆ J ⇔ I ⊆ J.
```

Thus, there is a [large Galois connection](order-theory.galois-connections.md) between the [large poset](order-theory.large-posets.md) of right ideals of `R` and the poset of subtractive right ideals of `R`.

## Definitions

### The universal property of the subtractive closure

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  (I : right-ideal-Semiring l2 R) (I' : subtractive-right-ideal-Semiring l3 R)
  where

  is-subtractive-closure-right-ideal-Semiring : UUω
  is-subtractive-closure-right-ideal-Semiring =
    {l4 : Level} (J : subtractive-right-ideal-Semiring l4 R) →
    leq-subtractive-right-ideal-Semiring R I' J ↔
    leq-right-ideal-Semiring R I
      ( right-ideal-subtractive-right-ideal-Semiring R J)

  contains-right-ideal-is-subtractive-closure-right-ideal-Semiring :
    is-subtractive-closure-right-ideal-Semiring →
    leq-right-ideal-Semiring R I
      ( right-ideal-subtractive-right-ideal-Semiring R I')
  contains-right-ideal-is-subtractive-closure-right-ideal-Semiring U =
    forward-implication (U I') (refl-leq-subtractive-right-ideal-Semiring R I')

  leq-is-subtractive-closure-right-ideal-Semiring :
    is-subtractive-closure-right-ideal-Semiring →
    {l4 : Level} (J : subtractive-right-ideal-Semiring l4 R) →
    leq-right-ideal-Semiring R I
      ( right-ideal-subtractive-right-ideal-Semiring R J) →
    leq-subtractive-right-ideal-Semiring R I' J
  leq-is-subtractive-closure-right-ideal-Semiring U J =
    backward-implication (U J)
```

### The universal property of the subtractive closure of a family of right ideals of a semiring

```agda
module _
  {l1 l2 l3 l4 : Level} (R : Semiring l1) {U : UU l2}
  (I : U → right-ideal-Semiring l3 R)
  (J : subtractive-right-ideal-Semiring l4 R)
  (H :
    (α : U) →
    leq-right-ideal-Semiring R
      ( I α)
      ( right-ideal-subtractive-right-ideal-Semiring R J))
  where

  is-subtractive-right-ideal-generated-by-family-of-right-ideals-Semiring : UUω
  is-subtractive-right-ideal-generated-by-family-of-right-ideals-Semiring =
    {l : Level} (K : subtractive-right-ideal-Semiring l R) →
    ( (α : U) →
      leq-right-ideal-Semiring R
        ( I α)
        ( right-ideal-subtractive-right-ideal-Semiring R K)) →
    leq-subtractive-right-ideal-Semiring R J K
```


### Construction of the subtractive closure Galois connection

#### The subtractive closure of an ideal

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : right-ideal-Semiring l2 R)
  where

  subset-subtractive-closure-right-ideal-Semiring :
    subset-Semiring (l1 ⊔ l2) R
  subset-subtractive-closure-right-ideal-Semiring x =
    ∃ ( type-Semiring R)
      ( λ y →
        subset-right-ideal-Semiring R I y ∧
        subset-right-ideal-Semiring R I (add-Semiring R x y))

  is-in-subtractive-closure-right-ideal-Semiring :
    type-Semiring R → UU (l1 ⊔ l2)
  is-in-subtractive-closure-right-ideal-Semiring =
    is-in-subset-Semiring R subset-subtractive-closure-right-ideal-Semiring

  is-prop-is-in-subtractive-closure-right-ideal-Semiring :
    (x : type-Semiring R) →
    is-prop (is-in-subtractive-closure-right-ideal-Semiring x)
  is-prop-is-in-subtractive-closure-right-ideal-Semiring =
    is-prop-is-in-subset-Semiring R
      subset-subtractive-closure-right-ideal-Semiring

  type-subtractive-closure-right-ideal-Semiring : UU (l1 ⊔ l2)
  type-subtractive-closure-right-ideal-Semiring =
    type-subset-Semiring R subset-subtractive-closure-right-ideal-Semiring

  inclusion-subtractive-closure-right-ideal-Semiring :
    type-subtractive-closure-right-ideal-Semiring → type-Semiring R
  inclusion-subtractive-closure-right-ideal-Semiring =
    inclusion-subset-Semiring R subset-subtractive-closure-right-ideal-Semiring

  ap-inclusion-subtractive-closure-right-ideal-Semiring :
    (x y : type-subtractive-closure-right-ideal-Semiring) → x ＝ y →
    inclusion-subtractive-closure-right-ideal-Semiring x ＝
    inclusion-subtractive-closure-right-ideal-Semiring y
  ap-inclusion-subtractive-closure-right-ideal-Semiring =
    ap-inclusion-subset-Semiring R
      subset-subtractive-closure-right-ideal-Semiring

  is-in-subset-inclusion-subtractive-closure-right-ideal-Semiring :
    (x : type-subtractive-closure-right-ideal-Semiring) →
    is-in-subtractive-closure-right-ideal-Semiring
      ( inclusion-subtractive-closure-right-ideal-Semiring x)
  is-in-subset-inclusion-subtractive-closure-right-ideal-Semiring =
    is-in-subset-inclusion-subset-Semiring R
      subset-subtractive-closure-right-ideal-Semiring

  is-closed-under-eq-subtractive-closure-right-ideal-Semiring :
    {x y : type-Semiring R} →
    is-in-subtractive-closure-right-ideal-Semiring x →
    (x ＝ y) → is-in-subtractive-closure-right-ideal-Semiring y
  is-closed-under-eq-subtractive-closure-right-ideal-Semiring =
    is-closed-under-eq-subset-Semiring R
      subset-subtractive-closure-right-ideal-Semiring

  is-closed-under-eq-subtractive-closure-right-ideal-Semiring' :
    {x y : type-Semiring R} →
    is-in-subtractive-closure-right-ideal-Semiring y →
    (x ＝ y) → is-in-subtractive-closure-right-ideal-Semiring x
  is-closed-under-eq-subtractive-closure-right-ideal-Semiring' =
    is-closed-under-eq-subset-Semiring' R
      subset-subtractive-closure-right-ideal-Semiring

  contains-right-ideal-subtractive-closure-right-ideal-Semiring :
    subset-right-ideal-Semiring R I ⊆
    subset-subtractive-closure-right-ideal-Semiring
  contains-right-ideal-subtractive-closure-right-ideal-Semiring x H =
    intro-exists
      ( zero-Semiring R)
      ( contains-zero-right-ideal-Semiring R I ,
        is-closed-under-addition-right-ideal-Semiring R I H
          ( contains-zero-right-ideal-Semiring R I))

  contains-zero-subtractive-closure-right-ideal-Semiring :
    is-in-subtractive-closure-right-ideal-Semiring (zero-Semiring R)
  contains-zero-subtractive-closure-right-ideal-Semiring =
    contains-right-ideal-subtractive-closure-right-ideal-Semiring _
      ( contains-zero-right-ideal-Semiring R I)

  is-closed-under-addition-subtractive-closure-right-ideal-Semiring :
    {x y : type-Semiring R} →
    is-in-subtractive-closure-right-ideal-Semiring x →
    is-in-subtractive-closure-right-ideal-Semiring y →
    is-in-subtractive-closure-right-ideal-Semiring (add-Semiring R x y)
  is-closed-under-addition-subtractive-closure-right-ideal-Semiring H K =
    apply-twice-universal-property-trunc-Prop H K
      ( subset-subtractive-closure-right-ideal-Semiring (add-Semiring R _ _))
      ( λ (u , u∈I , x+u∈I) (v , v∈I , y+v∈I) →
        intro-exists
          ( add-Semiring R u v)
          ( is-closed-under-addition-right-ideal-Semiring R I u∈I v∈I ,
            is-closed-under-eq-right-ideal-Semiring R I
              ( is-closed-under-addition-right-ideal-Semiring R I x+u∈I y+v∈I)
              ( interchange-add-add-Semiring R)))

  is-additive-submonoid-subtractive-closure-right-ideal-Semiring :
    is-additive-submonoid-subset-Semiring R
      subset-subtractive-closure-right-ideal-Semiring
  pr1 is-additive-submonoid-subtractive-closure-right-ideal-Semiring =
    contains-zero-subtractive-closure-right-ideal-Semiring
  pr2 is-additive-submonoid-subtractive-closure-right-ideal-Semiring =
    is-closed-under-addition-subtractive-closure-right-ideal-Semiring

  additive-submonoid-subtractive-closure-right-ideal-Semiring :
    Submonoid (l1 ⊔ l2) (additive-monoid-Semiring R)
  pr1 additive-submonoid-subtractive-closure-right-ideal-Semiring =
    subset-subtractive-closure-right-ideal-Semiring
  pr2 additive-submonoid-subtractive-closure-right-ideal-Semiring =
    is-additive-submonoid-subtractive-closure-right-ideal-Semiring

  is-closed-under-right-multiplication-subtractive-closure-right-ideal-Semiring :
    is-closed-under-right-multiplication-subset-Semiring R
      subset-subtractive-closure-right-ideal-Semiring
  is-closed-under-right-multiplication-subtractive-closure-right-ideal-Semiring
    H =
    apply-universal-property-trunc-Prop H
      ( subset-subtractive-closure-right-ideal-Semiring _)
      ( λ (u , u∈I , y+u∈I) →
        intro-exists
          ( mul-Semiring R u _)
          ( is-closed-under-right-multiplication-right-ideal-Semiring R I u∈I ,
            is-closed-under-eq-right-ideal-Semiring R I
              ( is-closed-under-right-multiplication-right-ideal-Semiring R I
                y+u∈I)
              ( right-distributive-mul-add-Semiring R _ _ _)))

  is-right-ideal-subtractive-closure-right-ideal-Semiring :
    is-right-ideal-subset-Semiring R
      subset-subtractive-closure-right-ideal-Semiring
  pr1 is-right-ideal-subtractive-closure-right-ideal-Semiring =
    is-additive-submonoid-subtractive-closure-right-ideal-Semiring
  pr2 is-right-ideal-subtractive-closure-right-ideal-Semiring =
    is-closed-under-right-multiplication-subtractive-closure-right-ideal-Semiring

  right-ideal-subtractive-closure-right-ideal-Semiring :
    right-ideal-Semiring (l1 ⊔ l2) R
  pr1 right-ideal-subtractive-closure-right-ideal-Semiring =
    subset-subtractive-closure-right-ideal-Semiring
  pr2 right-ideal-subtractive-closure-right-ideal-Semiring =
    is-right-ideal-subtractive-closure-right-ideal-Semiring

  is-subtractive-subtractive-closure-right-ideal-Semiring :
    is-subtractive-right-ideal-Semiring R
      right-ideal-subtractive-closure-right-ideal-Semiring
  is-subtractive-subtractive-closure-right-ideal-Semiring H K =
    apply-twice-universal-property-trunc-Prop H K
      ( subset-subtractive-closure-right-ideal-Semiring _)
      ( λ (u , u∈I , x+u∈I) (v , v∈I , x+y+v∈I) →
        intro-exists
          ( add-Semiring R _ (add-Semiring R v u))
          ( is-closed-under-eq-right-ideal-Semiring R I
              ( is-closed-under-addition-right-ideal-Semiring R I v∈I x+u∈I)
              ( left-swap-add-Semiring R) ,
            is-closed-under-eq-right-ideal-Semiring' R I
              ( is-closed-under-addition-right-ideal-Semiring R I x+y+v∈I u∈I)
              ( left-swap-add-Semiring R ∙
                inv (associative-add-Semiring R _ _ _) ∙
                inv (associative-add-Semiring R _ _ _))))

  subtractive-closure-right-ideal-Semiring :
    subtractive-right-ideal-Semiring (l1 ⊔ l2) R
  pr1 subtractive-closure-right-ideal-Semiring =
    right-ideal-subtractive-closure-right-ideal-Semiring
  pr2 subtractive-closure-right-ideal-Semiring =
    is-subtractive-subtractive-closure-right-ideal-Semiring

  forward-implication-is-subtractive-closure-subtractive-closure-right-ideal-Semiring :
    {l3 : Level} (J : subtractive-right-ideal-Semiring l3 R) →
    leq-subtractive-right-ideal-Semiring R
      subtractive-closure-right-ideal-Semiring J →
    leq-right-ideal-Semiring R I
      ( right-ideal-subtractive-right-ideal-Semiring R J)
  forward-implication-is-subtractive-closure-subtractive-closure-right-ideal-Semiring
    J H =
    transitive-leq-subtype
      ( subset-right-ideal-Semiring R I)
      ( subset-subtractive-closure-right-ideal-Semiring)
      ( subset-subtractive-right-ideal-Semiring R J)
      ( H)
      ( contains-right-ideal-subtractive-closure-right-ideal-Semiring)

  leq-subtractive-closure-right-ideal-Semiring :
    {l3 : Level} (J : subtractive-right-ideal-Semiring l3 R) →
    leq-right-ideal-Semiring R I
      ( right-ideal-subtractive-right-ideal-Semiring R J) →
    leq-subtractive-right-ideal-Semiring R
      ( subtractive-closure-right-ideal-Semiring)
      ( J)
  leq-subtractive-closure-right-ideal-Semiring
    J H x K =
    apply-universal-property-trunc-Prop K
      ( subset-subtractive-right-ideal-Semiring R J x)
      ( λ (u , u∈I , x+u∈I) →
        is-subtractive-subtractive-right-ideal-Semiring R J
          ( H u u∈I)
          ( is-closed-under-eq-subtractive-right-ideal-Semiring R J
            ( H (add-Semiring R x u) x+u∈I)
            ( commutative-add-Semiring R _ _)))

  is-subtractive-closure-subtractive-closure-right-ideal-Semiring :
    is-subtractive-closure-right-ideal-Semiring R I
      subtractive-closure-right-ideal-Semiring
  pr1 (is-subtractive-closure-subtractive-closure-right-ideal-Semiring J) =
    forward-implication-is-subtractive-closure-subtractive-closure-right-ideal-Semiring
      J
  pr2 (is-subtractive-closure-subtractive-closure-right-ideal-Semiring J) =
    leq-subtractive-closure-right-ideal-Semiring
      J
```

#### Subtractive closure is order preserving

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  preserves-order-subtractive-closure-right-ideal-Semiring :
    {l2 l3 : Level}
    (I : right-ideal-Semiring l2 R) (J : right-ideal-Semiring l3 R) →
    leq-right-ideal-Semiring R I J →
    leq-subtractive-right-ideal-Semiring R
      ( subtractive-closure-right-ideal-Semiring R I)
      ( subtractive-closure-right-ideal-Semiring R J)
  preserves-order-subtractive-closure-right-ideal-Semiring I J H =
    leq-subtractive-closure-right-ideal-Semiring R I
      ( subtractive-closure-right-ideal-Semiring R J)
      ( transitive-leq-right-ideal-Semiring R I J
        ( right-ideal-subtractive-closure-right-ideal-Semiring R J)
        ( contains-right-ideal-subtractive-closure-right-ideal-Semiring R J)
        ( H))

  subtractive-closure-right-ideal-hom-large-poset-Semiring :
    hom-Large-Poset
      ( λ l2 → l1 ⊔ l2)
      ( right-ideal-Semiring-Large-Poset R)
      ( subtractive-right-ideal-Semiring-Large-Poset R)
  map-hom-Large-Preorder
    subtractive-closure-right-ideal-hom-large-poset-Semiring =
    subtractive-closure-right-ideal-Semiring R
  preserves-order-hom-Large-Preorder
    subtractive-closure-right-ideal-hom-large-poset-Semiring =
    preserves-order-subtractive-closure-right-ideal-Semiring
```

#### The subtractive closure Galois connection

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  adjoint-relation-subtractive-closure-right-ideal-Semiring :
    {l2 l3 : Level}
    (I : right-ideal-Semiring l2 R)
    (J : subtractive-right-ideal-Semiring l3 R) →
    leq-subtractive-right-ideal-Semiring R
      ( subtractive-closure-right-ideal-Semiring R I)
      ( J) ↔
    leq-right-ideal-Semiring R I
      ( right-ideal-subtractive-right-ideal-Semiring R J)
  adjoint-relation-subtractive-closure-right-ideal-Semiring I J =
    is-subtractive-closure-subtractive-closure-right-ideal-Semiring R I J

  subtractive-closure-right-ideal-galois-connection-Semiring :
    galois-connection-Large-Poset
      ( λ l2 → l1 ⊔ l2)
      ( λ l → l)
      ( right-ideal-Semiring-Large-Poset R)
      ( subtractive-right-ideal-Semiring-Large-Poset R)
  lower-adjoint-galois-connection-Large-Poset
    subtractive-closure-right-ideal-galois-connection-Semiring =
    subtractive-closure-right-ideal-hom-large-poset-Semiring R
  upper-adjoint-galois-connection-Large-Poset
    subtractive-closure-right-ideal-galois-connection-Semiring =
    right-ideal-subtractive-right-ideal-hom-large-poset-Semiring R
  adjoint-relation-galois-connection-Large-Poset
    subtractive-closure-right-ideal-galois-connection-Semiring =
    adjoint-relation-subtractive-closure-right-ideal-Semiring
```

#### The subtractive closure reflective Galois connection

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  forward-inclusion-is-reflective-subtractive-closure-right-ideal-Semiring :
    {l2 : Level} (I : subtractive-right-ideal-Semiring l2 R) →
    leq-subtractive-right-ideal-Semiring R
      ( subtractive-closure-right-ideal-Semiring R
        ( right-ideal-subtractive-right-ideal-Semiring R I))
      ( I)
  forward-inclusion-is-reflective-subtractive-closure-right-ideal-Semiring I =
    leq-subtractive-closure-right-ideal-Semiring R
      ( right-ideal-subtractive-right-ideal-Semiring R I)
      ( I)
      ( refl-leq-subtractive-right-ideal-Semiring R I)

  backward-inclusion-is-reflective-subtractive-closure-right-ideal-Semiring :
    {l2 : Level} (I : subtractive-right-ideal-Semiring l2 R) →
    leq-subtractive-right-ideal-Semiring R I
      ( subtractive-closure-right-ideal-Semiring R
        ( right-ideal-subtractive-right-ideal-Semiring R I))
  backward-inclusion-is-reflective-subtractive-closure-right-ideal-Semiring I =
    contains-right-ideal-subtractive-closure-right-ideal-Semiring R
      ( right-ideal-subtractive-right-ideal-Semiring R I)

  is-reflective-subtractive-closure-right-ideal-Semiring :
    is-reflective-galois-connection-Large-Poset
      ( right-ideal-Semiring-Large-Poset R)
      ( subtractive-right-ideal-Semiring-Large-Poset R)
      ( subtractive-closure-right-ideal-galois-connection-Semiring R)
  pr1 (is-reflective-subtractive-closure-right-ideal-Semiring I) =
    forward-inclusion-is-reflective-subtractive-closure-right-ideal-Semiring I
  pr2 (is-reflective-subtractive-closure-right-ideal-Semiring I) =
    backward-inclusion-is-reflective-subtractive-closure-right-ideal-Semiring I

  subtractive-closure-right-ideal-reflective-galois-connection-Semiring :
    reflective-galois-connection-Large-Poset
      ( right-ideal-Semiring-Large-Poset R)
      ( subtractive-right-ideal-Semiring-Large-Poset R)
  galois-connection-reflective-galois-connection-Large-Poset
    subtractive-closure-right-ideal-reflective-galois-connection-Semiring =
    subtractive-closure-right-ideal-galois-connection-Semiring R
  is-reflective-reflective-galois-connection-Large-Poset
    subtractive-closure-right-ideal-reflective-galois-connection-Semiring =
    is-reflective-subtractive-closure-right-ideal-Semiring
```

### The subtractive right ideal generated by a family of right ideals of a semiring

```agda
module _
  {l1 l2 l3 : Level}
  (R : Semiring l1) {U : UU l2} (I : U → right-ideal-Semiring l3 R)
  where

  generating-right-ideal-subtractive-right-ideal-family-of-right-ideals-Semiring :
    right-ideal-Semiring (l1 ⊔ l2 ⊔ l3) R
  generating-right-ideal-subtractive-right-ideal-family-of-right-ideals-Semiring =
    join-family-of-right-ideals-Semiring R I

  subtractive-right-ideal-family-of-right-ideals-Semiring :
    subtractive-right-ideal-Semiring (l1 ⊔ l2 ⊔ l3) R
  subtractive-right-ideal-family-of-right-ideals-Semiring =
    subtractive-closure-right-ideal-Semiring R
      generating-right-ideal-subtractive-right-ideal-family-of-right-ideals-Semiring

  right-ideal-subtractive-right-ideal-family-of-right-ideals-Semiring :
    right-ideal-Semiring (l1 ⊔ l2 ⊔ l3) R
  right-ideal-subtractive-right-ideal-family-of-right-ideals-Semiring =
    right-ideal-subtractive-closure-right-ideal-Semiring R
      generating-right-ideal-subtractive-right-ideal-family-of-right-ideals-Semiring

  is-in-subtractive-right-ideal-family-of-right-ideals-Semiring :
    type-Semiring R → UU (l1 ⊔ l2 ⊔ l3)
  is-in-subtractive-right-ideal-family-of-right-ideals-Semiring =
    is-in-subtractive-closure-right-ideal-Semiring R
      generating-right-ideal-subtractive-right-ideal-family-of-right-ideals-Semiring

  contains-right-ideal-subtractive-right-ideal-family-of-right-ideals-Semiring :
    {α : U} →
    leq-right-ideal-Semiring R
      ( I α)
      ( right-ideal-subtractive-right-ideal-family-of-right-ideals-Semiring)
  contains-right-ideal-subtractive-right-ideal-family-of-right-ideals-Semiring =
    transitive-leq-right-ideal-Semiring R
      ( I _)
      ( generating-right-ideal-subtractive-right-ideal-family-of-right-ideals-Semiring)
      ( right-ideal-subtractive-right-ideal-family-of-right-ideals-Semiring)
      ( contains-right-ideal-subtractive-closure-right-ideal-Semiring R
        generating-right-ideal-subtractive-right-ideal-family-of-right-ideals-Semiring)
      ( contains-right-ideal-join-family-of-right-ideals-Semiring R I)

  is-subtractive-right-ideal-generated-by-family-of-right-ideals-subtractive-right-ideal-family-of-right-ideals-Semiring :
    is-subtractive-right-ideal-generated-by-family-of-right-ideals-Semiring R I
      ( subtractive-right-ideal-family-of-right-ideals-Semiring)
      ( λ α →
        contains-right-ideal-subtractive-right-ideal-family-of-right-ideals-Semiring)
  is-subtractive-right-ideal-generated-by-family-of-right-ideals-subtractive-right-ideal-family-of-right-ideals-Semiring
    J H =
    leq-subtractive-closure-right-ideal-Semiring R
      ( generating-right-ideal-subtractive-right-ideal-family-of-right-ideals-Semiring)
      ( J)
      ( leq-join-family-of-right-ideals-Semiring R I
        ( right-ideal-subtractive-right-ideal-Semiring R J)
        ( H))
```

## Properties

### The subtractive right ideal generated by the underlying right ideal of a subtractive right ideal `I` is `I` itself

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : subtractive-right-ideal-Semiring l2 R)
  where

  idempotent-subtractive-closure-right-ideal-Semiring :
    has-same-elements-subtractive-right-ideal-Semiring R
      ( subtractive-closure-right-ideal-Semiring R
        ( right-ideal-subtractive-right-ideal-Semiring R I))
      ( I)
  idempotent-subtractive-closure-right-ideal-Semiring =
    has-same-elements-sim-subtype
      ( subset-subtractive-closure-right-ideal-Semiring R
        ( right-ideal-subtractive-right-ideal-Semiring R I))
      ( subset-subtractive-right-ideal-Semiring R I)
      ( is-reflective-subtractive-closure-right-ideal-Semiring R I)
```

### Subtractive closure preserves least upper bounds

In
[`ring-theory.joins-subtractive-right-ideals-semirings`](ring-theory.joins-subtractive-right-ideals-semirings.md)
we will convert this fact to the fact that subtractive closure preserves joins.

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {U : UU l2} (I : U → right-ideal-Semiring l3 R)
  where

  preserves-least-upper-bounds-subtractive-closure-right-ideal-Semiring :
    {l4 : Level} (J : right-ideal-Semiring l4 R) →
    is-join-family-of-right-ideals-Semiring R
      ( I)
      ( J) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( subtractive-right-ideal-Semiring-Large-Poset R)
      ( λ α → subtractive-closure-right-ideal-Semiring R (I α))
      ( subtractive-closure-right-ideal-Semiring R J)
  preserves-least-upper-bounds-subtractive-closure-right-ideal-Semiring =
    preserves-join-lower-adjoint-galois-connection-Large-Poset
      ( right-ideal-Semiring-Large-Poset R)
      ( subtractive-right-ideal-Semiring-Large-Poset R)
      ( subtractive-closure-right-ideal-galois-connection-Semiring R)
      ( I)
```
