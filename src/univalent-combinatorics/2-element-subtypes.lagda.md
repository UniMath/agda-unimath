# `2`-element subtypes

```agda
module univalent-combinatorics.2-element-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphisms
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.mere-equivalences
open import foundation.negated-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-coproduct-types
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A 2-element subtype of a type `A` is a subtype `P` of `A` of which its
underlying type `Σ A P` has cardinality 2. Such a subtype is said to be
decidable if the proposition `P x` is decidable for every `x : A`.

## Definitions

### The type of 2-element subtypes of a type

```agda
2-Element-Subtype : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
2-Element-Subtype l2 X =
  Σ (subtype l2 X) (λ P → has-two-elements (type-subtype P))

module _
  {l1 l2 : Level} {X : UU l1} (P : 2-Element-Subtype l2 X)
  where

  subtype-2-Element-Subtype : subtype l2 X
  subtype-2-Element-Subtype = pr1 P

  type-prop-2-Element-Subtype : X → UU l2
  type-prop-2-Element-Subtype x = type-Prop (subtype-2-Element-Subtype x)

  is-prop-type-prop-2-Element-Subtype :
    (x : X) → is-prop (type-prop-2-Element-Subtype x)
  is-prop-type-prop-2-Element-Subtype x =
    is-prop-type-Prop (subtype-2-Element-Subtype x)

  type-2-Element-Subtype : UU (l1 ⊔ l2)
  type-2-Element-Subtype = type-subtype subtype-2-Element-Subtype

  inclusion-2-Element-Subtype : type-2-Element-Subtype → X
  inclusion-2-Element-Subtype = inclusion-subtype subtype-2-Element-Subtype

  is-emb-inclusion-2-Element-Subtype : is-emb inclusion-2-Element-Subtype
  is-emb-inclusion-2-Element-Subtype =
    is-emb-inclusion-subtype subtype-2-Element-Subtype

  is-injective-inclusion-2-Element-Subtype :
    is-injective inclusion-2-Element-Subtype
  is-injective-inclusion-2-Element-Subtype =
    is-injective-inclusion-subtype subtype-2-Element-Subtype

  has-two-elements-type-2-Element-Subtype :
    has-two-elements type-2-Element-Subtype
  has-two-elements-type-2-Element-Subtype = pr2 P

  2-element-type-2-Element-Subtype : 2-Element-Type (l1 ⊔ l2)
  pr1 2-element-type-2-Element-Subtype = type-2-Element-Subtype
  pr2 2-element-type-2-Element-Subtype = has-two-elements-type-2-Element-Subtype

  is-inhabited-type-2-Element-Subtype : type-trunc-Prop type-2-Element-Subtype
  is-inhabited-type-2-Element-Subtype =
    is-inhabited-2-Element-Type 2-element-type-2-Element-Subtype
```

### The standard 2-element subtype of a pair of distinct elements in a set

```agda
module _
  {l : Level} (X : Set l) {x y : type-Set X} (np : x ≠ y)
  where

  type-prop-standard-2-Element-Subtype : type-Set X → UU l
  type-prop-standard-2-Element-Subtype z = (x ＝ z) + (y ＝ z)

  is-prop-type-prop-standard-2-Element-Subtype :
    (z : type-Set X) → is-prop (type-prop-standard-2-Element-Subtype z)
  is-prop-type-prop-standard-2-Element-Subtype z =
    is-prop-coproduct
      ( λ p q → np (p ∙ inv q))
      ( is-set-type-Set X x z)
      ( is-set-type-Set X y z)

  subtype-standard-2-Element-Subtype : subtype l (type-Set X)
  pr1 (subtype-standard-2-Element-Subtype z) =
    type-prop-standard-2-Element-Subtype z
  pr2 (subtype-standard-2-Element-Subtype z) =
    is-prop-type-prop-standard-2-Element-Subtype z

  type-standard-2-Element-Subtype : UU l
  type-standard-2-Element-Subtype =
    type-subtype subtype-standard-2-Element-Subtype

  equiv-type-standard-2-Element-Subtype :
    Fin 2 ≃ type-standard-2-Element-Subtype
  equiv-type-standard-2-Element-Subtype =
    ( inv-equiv
      ( left-distributive-Σ-coproduct)) ∘e
    ( equiv-coproduct
      ( equiv-is-contr
        ( is-contr-Fin-1)
        ( is-torsorial-Id x))
      ( equiv-is-contr
        ( is-contr-unit)
        ( is-torsorial-Id y)))

  has-two-elements-type-standard-2-Element-Subtype :
    has-two-elements type-standard-2-Element-Subtype
  has-two-elements-type-standard-2-Element-Subtype =
    unit-trunc-Prop equiv-type-standard-2-Element-Subtype
```

### Morphisms of 2-element-subtypes

A moprhism of 2-element subtypes `P` and `Q` is just a family of maps
`P x → Q x`.

```agda
{-
module _
  {l1 l2 l3 : Level} {X : UU l1}
  (P : 2-Element-Subtype l2 X) (Q : 2-Element-Subtype l3 X)
  where

  hom-2-Element-Subtype : UU (l1 ⊔ l2 ⊔ l3)
  hom-2-Element-Subtype =
    (x : X) → type-prop-2-Element-Subtype P x → type-prop-2-Element-Subtype Q x

  map-hom-2-Element-Subtype :
    hom-2-Element-Subtype → type-2-Element-Subtype P → type-2-Element-Subtype Q
  map-hom-2-Element-Subtype f = tot f

  is-emb-map-hom-2-Element-Subtype :
    (f : hom-2-Element-Subtype) → is-emb (map-hom-2-Element-Subtype f)
  is-emb-map-hom-2-Element-Subtype f =
    is-emb-tot
      ( λ x →
        is-emb-is-prop
          ( is-prop-type-prop-2-Element-Subtype P x)
          ( is-prop-type-prop-2-Element-Subtype Q x))

  is-surjective-map-hom-2-Element-Subtype :
    (f : hom-2-Element-Subtype) → is-surjective (map-hom-2-Element-Subtype f)
  is-surjective-map-hom-2-Element-Subtype f (pair x q) = {! type-subtype (P ∘ map-inv-equiv e) !}

  is-equiv-map-hom-2-Element-Subtype :
    (f : hom-2-Element-Subtype) → is-equiv (map-hom-2-Element-Subtype f)
  is-equiv-map-hom-2-Element-Subtype f = {!!}
-}
```

### Swapping the elements in a 2-element subtype

```agda
module _
  {l1 l2 : Level} {X : UU l1} (P : 2-Element-Subtype l2 X)
  where

  swap-2-Element-Subtype : Aut (type-2-Element-Subtype P)
  swap-2-Element-Subtype =
    swap-2-Element-Type (2-element-type-2-Element-Subtype P)

  map-swap-2-Element-Subtype :
    type-2-Element-Subtype P → type-2-Element-Subtype P
  map-swap-2-Element-Subtype =
    map-swap-2-Element-Type (2-element-type-2-Element-Subtype P)

  compute-swap-2-Element-Subtype :
    (x y : type-2-Element-Subtype P) → x ≠ y →
    map-swap-2-Element-Subtype x ＝ y
  compute-swap-2-Element-Subtype =
    compute-swap-2-Element-Type (2-element-type-2-Element-Subtype P)
```

### 2-element subtypes are closed under precomposition with an equivalence

```agda
precomp-equiv-2-Element-Subtype :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} → X ≃ Y →
    2-Element-Subtype l3 X → 2-Element-Subtype l3 Y
pr1 (precomp-equiv-2-Element-Subtype e (pair P H)) =
  P ∘ (map-inv-equiv e)
pr2 (precomp-equiv-2-Element-Subtype e (pair P H)) =
  transitive-mere-equiv _ _ _
    ( unit-trunc-Prop
      ( equiv-subtype-equiv
        ( e)
        ( P)
        ( P ∘ (map-inv-equiv e))
        ( λ x →
          iff-equiv
            ( tr
              ( λ g → (type-Prop (P x)) ≃ (type-Prop (P (map-equiv g x))))
              ( inv (left-inverse-law-equiv e))
              ( id-equiv)))))
    ( H)

{-
module _
  {l : Level} {A : UU l}
  where

  is-injective-map-Fin-2 :
    (f : Fin 2 → A) → f zero-Fin ≠ f one-Fin → is-injective f
  is-injective-map-Fin-2 f H {inl (inr star)} {inl (inr star)} p = refl
  is-injective-map-Fin-2 f H {inl (inr star)} {inr star} p = ex-falso (H p)
  is-injective-map-Fin-2 f H {inr star} {inl (inr star)} p =
    ex-falso (H (inv p))
  is-injective-map-Fin-2 f H {inr star} {inr star} p = refl

  is-injective-element-unordered-pair :
    (p : unordered-pair A) →
    ¬ ( (x y : type-unordered-pair p) →
        Id (element-unordered-pair p x) (element-unordered-pair p y)) →
    is-injective (element-unordered-pair p)
  is-injective-element-unordered-pair (pair X f) H {x} {y} p =
    apply-universal-property-trunc-Prop
      ( has-two-elements-type-unordered-pair (pair X f))
      ( Id-Prop (set-Type-With-Cardinality-ℕ X) x y)
      ( λ h → {!!})
    where
    first-element : (Fin 2 ≃ (type-2-Element-Type X)) →
      Σ ( type-2-Element-Type X)
        ( λ x → ¬ ((y : type-2-Element-Type X) → Id (f x) (f y)))
    first-element h =
      exists-not-not-for-all-count (λ z → (w : type-2-Element-Type X) →
      Id (f z) (f w)) (λ z → {!!})
        {!!} {!!}
    two-elements-different-image :
      Σ ( type-2-Element-Type X)
        ( λ x → Σ (type-2-Element-Type X) (λ y → f x ≠ f y))
    two-elements-different-image = {!!}
-}
```
