# Intersections of subtypes

```agda
module foundation.intersections-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-locale-of-subtypes
open import foundation.powersets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.decidable-propositions
open import foundation-core.propositions

open import order-theory.greatest-lower-bounds-large-posets
```

</details>

## Idea

The intersection of two subtypes `A` and `B` is the subtype that contains the
elements that are in `A` and in `B`.

## Definition

### The intersection of two subtypes

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} (P : subtype l2 X) (Q : subtype l3 X)
  where

  intersection-subtype : subtype (l2 ⊔ l3) X
  intersection-subtype = meet-powerset-Large-Locale P Q

  is-greatest-binary-lower-bound-intersection-subtype :
    is-greatest-binary-lower-bound-Large-Poset
      ( powerset-Large-Poset X)
      ( P)
      ( Q)
      ( intersection-subtype)
  pr1
    ( pr1
      ( is-greatest-binary-lower-bound-intersection-subtype R)
      ( p , q) x r) =
    p x r
  pr2
    ( pr1
      ( is-greatest-binary-lower-bound-intersection-subtype R)
      ( p , q) x r) = q x r
  pr1 (pr2 (is-greatest-binary-lower-bound-intersection-subtype R) p) x r =
    pr1 (p x r)
  pr2 (pr2 (is-greatest-binary-lower-bound-intersection-subtype R) p) x r =
    pr2 (p x r)

  infixr 15 _∩_
  _∩_ = intersection-subtype
```

### The intersection of two decidable subtypes

```agda
module _
  {l l1 l2 : Level} {X : UU l}
  where

  intersection-decidable-subtype :
    decidable-subtype l1 X → decidable-subtype l2 X →
    decidable-subtype (l1 ⊔ l2) X
  intersection-decidable-subtype P Q x = conjunction-Decidable-Prop (P x) (Q x)
```

### The intersection of a family of subtypes

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1}
  where

  intersection-family-of-subtypes :
    {I : UU l2} (P : I → subtype l3 X) → subtype (l2 ⊔ l3) X
  intersection-family-of-subtypes {I} P x = Π-Prop I (λ i → P i x)
```

## TODO: Change title

```agda
-- It's too simple =)
-- module _
--   {l1 l2 l3 : Level} {X : UU l1} (P : subtype l2 X) (Q : subtype l3 X)
--   where

--   is-commutative-subtype-intersection :
--     P ∩ Q ⊆ Q ∩ P
--   is-commutative-subtype-intersection x (in-P , in-Q) = in-Q , in-P

module _
  {l1 l2 l3 : Level} {X : UU l1} (P : subtype l2 X) (Q : subtype l3 X)
  where

  subtype-intersection-left : P ∩ Q ⊆ P
  subtype-intersection-left _ = pr1

  subtype-intersection-right : P ∩ Q ⊆ Q
  subtype-intersection-right _ = pr2

  subtype-both-intersection :
    {l4 : Level} (S : subtype l4 X) →
    S ⊆ P → S ⊆ Q → S ⊆ P ∩ Q
  pr1 (subtype-both-intersection S S-sub-P S-sub-Q x in-S) = S-sub-P x in-S
  pr2 (subtype-both-intersection S S-sub-P S-sub-Q x in-S) = S-sub-Q x in-S

  intersection-subtype-left-subtype : P ⊆ Q → P ⊆ P ∩ Q
  intersection-subtype-left-subtype P-sub-Q =
    subtype-both-intersection P (refl-leq-subtype P) P-sub-Q

  intersection-subtype-right-subtype : Q ⊆ P → Q ⊆ P ∩ Q
  intersection-subtype-right-subtype Q-sub-P =
    subtype-both-intersection Q Q-sub-P (refl-leq-subtype Q)

  equiv-intersection-subtype-left :
    P ⊆ Q → equiv-subtypes (P ∩ Q) P
  equiv-intersection-subtype-left P-sub-Q =
    equiv-antisymmetric-leq-subtype
      ( P ∩ Q)
      ( P)
      ( subtype-intersection-left)
      ( intersection-subtype-left-subtype P-sub-Q)

  equiv-intersection-subtype-right :
    Q ⊆ P → equiv-subtypes (P ∩ Q) Q
  equiv-intersection-subtype-right Q-sub-P =
    equiv-antisymmetric-leq-subtype
      ( P ∩ Q)
      ( Q)
      ( subtype-intersection-right)
      ( intersection-subtype-right-subtype Q-sub-P)

module _
  {l1 : Level} {X : UU l1}
  where

  is-reflexivity-intersection :
    {l2 : Level} (P : subtype l2 X) → P ∩ P ＝ P
  is-reflexivity-intersection P =
    antisymmetric-leq-subtype _ _
      ( subtype-intersection-left P P)
      ( subtype-both-intersection
        ( P)
        ( P)
        ( P)
        ( refl-leq-subtype P)
        ( refl-leq-subtype P))

  is-commutative-subtype-intersection :
    {l2 l3 : Level} (P : subtype l2 X) (Q : subtype l3 X) →
    P ∩ Q ⊆ Q ∩ P
  is-commutative-subtype-intersection P Q =
    subtype-both-intersection Q P
      ( P ∩ Q)
      ( subtype-intersection-right P Q)
      ( subtype-intersection-left P Q)

  is-commutative-intersection :
    {l2 l3 : Level} (P : subtype l2 X) (Q : subtype l3 X) →
    P ∩ Q ＝ Q ∩ P
  is-commutative-intersection P Q =
    antisymmetric-leq-subtype _ _
      ( is-commutative-subtype-intersection P Q)
      ( is-commutative-subtype-intersection Q P)

  intersection-subtype-left-sublevels :
    {l2 : Level} (l3 : Level) (P : subtype (l2 ⊔ l3) X) (Q : subtype l2 X) →
    P ⊆ Q → P ∩ Q ＝ P
  intersection-subtype-left-sublevels _ P Q P-sub-Q =
    antisymmetric-leq-subtype _ _
      ( subtype-intersection-left P Q)
      ( intersection-subtype-left-subtype P Q P-sub-Q)

  intersection-subtype-right-sublevels :
    {l2 : Level} (l3 : Level) (P : subtype l2 X) (Q : subtype (l2 ⊔ l3) X) →
    Q ⊆ P → P ∩ Q ＝ Q
  intersection-subtype-right-sublevels l3 P Q Q-sub-P =
    tr
      ( _＝ Q)
      ( is-commutative-intersection Q P)
      ( intersection-subtype-left-sublevels l3 Q P Q-sub-P)

  intersection-subtype-left :
    {l2 : Level} (P Q : subtype l2 X) →
    P ⊆ Q → P ∩ Q ＝ P
  intersection-subtype-left = intersection-subtype-left-sublevels lzero

  intersection-subtype-right :
    {l2 : Level} (P Q : subtype l2 X) →
    Q ⊆ P → P ∩ Q ＝ Q
  intersection-subtype-right = intersection-subtype-right-sublevels lzero
```
