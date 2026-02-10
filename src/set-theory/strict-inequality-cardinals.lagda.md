# Strict inequality on cardinals

```agda
module set-theory.strict-inequality-cardinals where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cantor-schroder-bernstein-decidable-embeddings
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.decidable-embeddings
open import foundation.decidable-equality
open import foundation.decidable-maps
open import foundation.decidable-type-families
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.injective-maps
open import foundation.large-binary-relations
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.mere-embeddings
open import foundation.negation
open import foundation.nonsurjective-maps
open import foundation.projective-types
open import foundation.propositional-extensionality
open import foundation.propositional-maps
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.retractions
open import foundation.set-truncations
open import foundation.sets
open import foundation.surjective-maps
open import foundation.types-with-decidable-existential-quantification
open import foundation.univalence
open import foundation.universe-levels
open import foundation.weak-limited-principle-of-omniscience

open import logic.propositionally-decidable-types

open import set-theory.cardinals
open import set-theory.cardinals-with-decidable-existential-quantification
open import set-theory.complemented-inequality-cardinals
open import set-theory.discrete-cardinals
open import set-theory.inequality-cardinals
open import set-theory.inhabited-cardinals
open import set-theory.projective-cardinals
open import set-theory.strict-complemented-inequality-cardinals
open import set-theory.strict-indexed-inequality-cardinals
```

</details>

## Idea

We may say a [cardinal](set-theory.cardinals.md) `X` is (strictly)
{{#concept "less than" Disambiguation="set-cardinal" Agda=le-Cardinal}} a
cardinal `Y` if `X ≤ Y` and `Y ≰ X`, in the sense that every set in the
equivalence class of `X` merely embeds into every set in the equivalence class
of `Y`, and no set in the equivalence class of `Y` merely embeds into any set in
the equivalence class of `X`.

## Definition

### Strict inequality of cardinals

```agda
module _
  {l1 l2 : Level}
  where

  le-prop-Cardinal :
    Cardinal l1 → Cardinal l2 → Prop (l1 ⊔ l2)
  le-prop-Cardinal X Y =
    product-Prop
      ( leq-prop-Cardinal X Y)
      ( neg-Prop (leq-prop-Cardinal Y X))

  le-Cardinal : Cardinal l1 → Cardinal l2 → UU (l1 ⊔ l2)
  le-Cardinal X Y = type-Prop (le-prop-Cardinal X Y)
```

### Strict inequality of cardinalities of sets

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  le-prop-cardinality : Prop (l1 ⊔ l2)
  le-prop-cardinality =
    le-prop-Cardinal (cardinality X) (cardinality Y)

  le-cardinality : UU (l1 ⊔ l2)
  le-cardinality =
    le-Cardinal (cardinality X) (cardinality Y)

  is-prop-le-cardinality : is-prop le-cardinality
  is-prop-le-cardinality =
    is-prop-type-Prop le-prop-cardinality
```

## Properties

### If `Y` is inhabited-or-empty and `Y ≰ X` then `Y` is inhabited

```agda
module _
  {l1 l2 : Level}
  (X : Set l1) (Y : Set l2)
  (dY : is-inhabited-or-empty (type-Set Y))
  where

  is-inhabited-is-not-leq-cardinality :
    ¬ leq-cardinality Y X → is-inhabited (type-Set Y)
  is-inhabited-is-not-leq-cardinality H =
    rec-coproduct
      ( id)
      ( λ ny →
        ex-falso
          ( H ( unit-leq-cardinality Y X
                ( mere-emb-is-empty ny))))
      ( dY)
```

### Projective codomain implies surjections induce reverse embeddings

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  geq-is-surjective-cardinality :
    is-projective-Level' (l1 ⊔ l2) (type-Set Y) →
    (f : type-Set X → type-Set Y) →
    is-surjective f →
    leq-cardinality Y X
  geq-is-surjective-cardinality is-projective-Y f is-surjective-f =
    unit-leq-cardinality Y X
      ( map-trunc-Prop
        ( λ s →
          ( pr1 ∘ s ,
            is-emb-is-injective
              ( is-set-type-Set X)
              ( is-injective-has-retraction (pr1 ∘ s) f (pr2 ∘ s))))
        ( is-projective-Y (fiber f) is-surjective-f))
```

### Strict indexed inequality implies strict inequality assuming inequality

```agda
module _
  {l1 l2 : Level}
  (lem : level-LEM (l1 ⊔ l2))
  (X : Set l1) (Y : Set l2)
  where

  not-geq-le-indexed-leq-cardinality :
    leq-cardinality X Y →
    le-indexed-cardinality X Y →
    ¬ leq-cardinality Y X
  not-geq-le-indexed-leq-cardinality X≤Y X<Y Y≤X =
    rec-trunc-Prop
      ( empty-Prop)
      ( λ e →
        is-not-surjective-is-nonsurjective
          ( pr2
            ( inv-unit-le-indexed-cardinality X Y X<Y)
            ( map-equiv e))
          ( is-surjective-map-equiv e))
      ( antisymmetric-mere-emb
        ( lem)
        ( inv-unit-leq-cardinality X Y X≤Y)
        ( inv-unit-leq-cardinality Y X Y≤X))

  le-le-indexed-leq-cardinality :
    leq-cardinality X Y →
    le-indexed-cardinality X Y →
    le-cardinality X Y
  le-le-indexed-leq-cardinality X≤Y X<Y =
    ( X≤Y , not-geq-le-indexed-leq-cardinality X≤Y X<Y)
```

### Strict indexed inequality implies strict inequality from WLPO and decidable embeddings

```agda
module _
  {l1 l2 : Level}
  (wlpo : level-WLPO (l1 ⊔ l2))
  (X : Set l1) (Y : Set l2)
  (decidable-equality-X : has-decidable-equality (type-Set X))
  (decidable-∃-X :
    type-trunc-Prop (has-decidable-∃-Level l2 (type-Set X)))
  (decidable-equality-Y : has-decidable-equality (type-Set Y))
  (decidable-∃-Y :
    type-trunc-Prop (has-decidable-∃-Level l1 (type-Set Y)))
  where

  private
    is-decidable-is-inhabited-or-empty-is-prop :
      {l : Level} {A : UU l} →
      is-prop A → is-inhabited-or-empty A → is-decidable A
    is-decidable-is-inhabited-or-empty-is-prop {A = A} is-prop-A (inl |a|) =
      inl (rec-trunc-Prop (A , is-prop-A) id |a|)
    is-decidable-is-inhabited-or-empty-is-prop _ (inr na) = inr na

    is-decidable-map-emb-has-decidable-∃ :
      {lA lB : Level} {A : UU lA} {B : UU lB} →
      has-decidable-∃-Level lB A →
      has-decidable-equality B →
      (e : A ↪ B) →
      is-decidable-map (pr1 e)
    is-decidable-map-emb-has-decidable-∃ h∃A dB e y =
      is-decidable-is-inhabited-or-empty-is-prop
        ( is-prop-map-emb e y)
        ( is-inhabited-or-empty-map-has-decidable-∃-Level h∃A dB (pr1 e) y)

    decidable-emb-emb-XY :
      has-decidable-∃-Level l2 (type-Set X) →
      type-Set X ↪ type-Set Y → type-Set X ↪ᵈ type-Set Y
    decidable-emb-emb-XY h∃X e =
      ( pr1 e ,
        ( pr2 e ,
          is-decidable-map-emb-has-decidable-∃
            ( h∃X)
            ( decidable-equality-Y)
            ( e)))

    decidable-emb-emb-YX :
      has-decidable-∃-Level l1 (type-Set Y) →
      type-Set Y ↪ type-Set X → type-Set Y ↪ᵈ type-Set X
    decidable-emb-emb-YX h∃Y e =
      ( pr1 e ,
        ( pr2 e ,
          is-decidable-map-emb-has-decidable-∃
            ( h∃Y)
            ( decidable-equality-X)
            ( e)))

    leq-complemented-cardinality-of-leq-cardinality :
      leq-cardinality X Y → leq-complemented-cardinality X Y
    leq-complemented-cardinality-of-leq-cardinality X≤Y =
      rec-trunc-Prop
        ( leq-complemented-cardinality X Y ,
          is-prop-leq-complemented-cardinality X Y)
        ( λ h∃X →
          unit-leq-complemented-cardinality X Y
            ( map-trunc-Prop
              ( decidable-emb-emb-XY h∃X)
              ( inv-unit-leq-cardinality X Y X≤Y)))
        ( decidable-∃-X)

    leq-complemented-cardinality-of-leq-cardinality' :
      leq-cardinality Y X → leq-complemented-cardinality Y X
    leq-complemented-cardinality-of-leq-cardinality' Y≤X =
      rec-trunc-Prop
        ( leq-complemented-cardinality Y X ,
          is-prop-leq-complemented-cardinality Y X)
        ( λ h∃Y →
          unit-leq-complemented-cardinality Y X
            ( map-trunc-Prop
              ( decidable-emb-emb-YX h∃Y)
              ( inv-unit-leq-cardinality Y X Y≤X)))
        ( decidable-∃-Y)

  not-geq-le-indexed-leq-cardinality-WLPO :
    leq-cardinality X Y →
    le-indexed-cardinality X Y →
    ¬ leq-cardinality Y X
  not-geq-le-indexed-leq-cardinality-WLPO X≤Y X<Y Y≤X =
    not-geq-complemented-le-indexed-leq-complemented-cardinality
      ( wlpo)
      ( X)
      ( Y)
      ( leq-complemented-cardinality-of-leq-cardinality X≤Y)
      ( X<Y)
      ( leq-complemented-cardinality-of-leq-cardinality' Y≤X)

  le-le-indexed-leq-cardinality-WLPO :
    leq-cardinality X Y →
    le-indexed-cardinality X Y →
    le-cardinality X Y
  le-le-indexed-leq-cardinality-WLPO X≤Y X<Y =
    ( X≤Y , not-geq-le-indexed-leq-cardinality-WLPO X≤Y X<Y)
```

### Strict inequality implies strict indexed inequality under projectivity

```agda
module _
  {l1 l2 : Level}
  (X : Set l1) (Y : Set l2)
  (decidable-∃-X :
    type-trunc-Prop (has-decidable-∃-Level l2 (type-Set X)))
  (is-projective-Y : is-projective-Level' (l1 ⊔ l2) (type-Set Y))
  (decidable-equality-Y : has-decidable-equality (type-Set Y))
  (decidable-∃-Y :
    type-trunc-Prop (has-decidable-∃-Level (l1 ⊔ l2) (type-Set Y)))
  where

  le-indexed-le-cardinality :
    le-cardinality X Y →
    le-indexed-cardinality X Y
  le-indexed-le-cardinality (_ , nY≤X) =
    unit-le-indexed-cardinality X Y
      ( is-inhabited-is-not-leq-cardinality X Y
          ( is-inhabited-or-empty-merely-has-decidable-∃-Level decidable-∃-Y)
          ( nY≤X) ,
        λ f →
          apply-twice-universal-property-trunc-Prop
            decidable-∃-Y
            decidable-∃-X
            ( is-nonsurjective-Prop f)
            ( λ hΣY hΣX →
              is-nonsurjective-is-not-surjective-has-decidable-∃-is-inhabited-or-empty-map
                hΣY
                ( is-inhabited-or-empty-map-has-decidable-∃-Level
                  hΣX decidable-equality-Y f)
                ( nY≤X ∘
                  geq-is-surjective-cardinality X Y is-projective-Y f)
            )
      )

module _
  {l1 l2 : Level}
  (lem : level-LEM (l1 ⊔ l2))
  (X : Set l1) (Y : Set l2)
  (is-projective-Y : is-projective-Level' (l1 ⊔ l2) (type-Set Y))
  where

  private
    is-decidable-trunc-Prop-LEM :
      is-decidable (type-trunc-Prop (type-Set Y))
    is-decidable-trunc-Prop-LEM =
      is-decidable-equiv
        ( compute-raise l1 (type-trunc-Prop (type-Set Y)))
        ( lem (raise-Prop l1 (is-inhabited-Prop (type-Set Y))))

    is-inhabited-or-empty-LEM :
      is-inhabited-or-empty (type-Set Y)
    is-inhabited-or-empty-LEM =
      is-inhabited-or-empty-is-decidable-trunc-Prop
        ( is-decidable-trunc-Prop-LEM)

  le-indexed-le-cardinality-LEM :
    le-cardinality X Y →
    le-indexed-cardinality X Y
  le-indexed-le-cardinality-LEM (_ , nY≤X) =
    unit-le-indexed-cardinality X Y
      ( is-inhabited-is-not-leq-cardinality X Y
          ( is-inhabited-or-empty-LEM)
          ( nY≤X) ,
        λ f →
        is-nonsurjective-is-not-surjective-LEM
          ( lem)
          ( nY≤X ∘
            geq-is-surjective-cardinality X Y is-projective-Y f))

module _
  {l1 l2 : Level}
  (lem : level-LEM (l1 ⊔ l2))
  (X : Set l1) (Y : Set l2)
  (decidable-∃-X :
    type-trunc-Prop (has-decidable-∃-Level l2 (type-Set X)))
  (is-projective-Y : is-projective-Level' (l1 ⊔ l2) (type-Set Y))
  (decidable-equality-Y : has-decidable-equality (type-Set Y))
  (decidable-∃-Y :
    type-trunc-Prop (has-decidable-∃-Level (l1 ⊔ l2) (type-Set Y)))
  where

  le-iff-le-indexed-cardinality :
    leq-cardinality X Y →
    le-indexed-cardinality X Y ↔ le-cardinality X Y
  le-iff-le-indexed-cardinality X≤Y =
    ( le-le-indexed-leq-cardinality lem X Y X≤Y ,
      le-indexed-le-cardinality X Y decidable-∃-X
        is-projective-Y decidable-equality-Y decidable-∃-Y)

module _
  {l1 l2 : Level}
  (wlpo : level-WLPO (l1 ⊔ l2))
  (X : Set l1) (Y : Set l2)
  (decidable-equality-X : has-decidable-equality (type-Set X))
  (decidable-∃-X :
    type-trunc-Prop (has-decidable-∃-Level l2 (type-Set X)))
  (is-projective-Y : is-projective-Level' (l1 ⊔ l2) (type-Set Y))
  (decidable-equality-Y : has-decidable-equality (type-Set Y))
  (decidable-∃-Y :
    type-trunc-Prop (has-decidable-∃-Level (l1 ⊔ l2) (type-Set Y)))
  where

  private
    has-decidable-∃-Level-lower :
      {lA l2 l3 : Level} {A : UU lA} →
      has-decidable-∃-Level (l2 ⊔ l3) A →
      has-decidable-∃-Level l2 A
    has-decidable-∃-Level-lower {lA} {l2} {l3} {A} h P =
      let
        raise-decidable-family :
          decidable-family l2 A → decidable-family (l2 ⊔ l3) A
        raise-decidable-family Q =
          ( (λ a → raise l3 (family-decidable-family Q a)) ,
            ( λ a →
              is-decidable-equiv'
                ( compute-raise l3 (family-decidable-family Q a))
                ( is-decidable-decidable-family Q a)))
      in
      is-decidable-equiv'
        ( equiv-trunc-Prop
          ( equiv-tot
            ( λ a →
              inv-equiv (compute-raise l3 (family-decidable-family P a)))))
        ( h (raise-decidable-family P))

    decidable-∃-Y-l1 :
      type-trunc-Prop (has-decidable-∃-Level l1 (type-Set Y))
    decidable-∃-Y-l1 =
      map-trunc-Prop
        ( has-decidable-∃-Level-lower {l2 = l1} {l3 = l2})
        ( decidable-∃-Y)

  le-iff-le-indexed-cardinality-WLPO :
    leq-cardinality X Y →
    le-indexed-cardinality X Y ↔ le-cardinality X Y
  le-iff-le-indexed-cardinality-WLPO X≤Y =
    ( le-le-indexed-leq-cardinality-WLPO
        ( wlpo)
        ( X)
        ( Y)
        ( decidable-equality-X)
        ( decidable-∃-X)
        ( decidable-equality-Y)
        ( decidable-∃-Y-l1)
        ( X≤Y) ,
      le-indexed-le-cardinality X Y decidable-∃-X
        is-projective-Y decidable-equality-Y decidable-∃-Y)
```

### Strict inequality implies strict indexed inequality for projective cardinals

```agda
module _
  {l1 l2 : Level}
  where

  le-indexed-le-Cardinal :
    (X : Cardinal l1) (Y : Cardinal l2) →
    merely-decidable-∃-Cardinal l2 X →
    is-projective-Cardinal (l1 ⊔ l2) Y →
    is-discrete-Cardinal Y →
    merely-decidable-∃-Cardinal (l1 ⊔ l2) Y →
    le-Cardinal X Y →
    le-indexed-Cardinal X Y
  le-indexed-le-Cardinal =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ X Y →
        set-Prop
          ( function-Prop
            ( merely-decidable-∃-Cardinal l2 X)
            ( function-Prop
              ( is-projective-Cardinal (l1 ⊔ l2) Y)
              ( function-Prop
                ( is-discrete-Cardinal Y)
                ( function-Prop
                  ( merely-decidable-∃-Cardinal (l1 ⊔ l2) Y)
                  ( function-Prop
                    ( le-Cardinal X Y)
                    ( le-indexed-prop-Cardinal X Y)))))))
      ( λ X Y merely-Σ-X is-projective-Y is-discrete-Y merely-Σ-Y →
        le-indexed-le-cardinality
          ( X)
          ( Y)
          ( inv-unit-merely-decidable-∃-cardinality X merely-Σ-X)
          ( inv-unit-is-projective-cardinality Y is-projective-Y)
          ( inv-unit-is-discrete-cardinality Y is-discrete-Y)
          ( inv-unit-merely-decidable-∃-cardinality Y merely-Σ-Y))

  le-iff-le-indexed-Cardinal :
    (lem : level-LEM (l1 ⊔ l2)) →
    (X : Cardinal l1) (Y : Cardinal l2) →
    merely-decidable-∃-Cardinal l2 X →
    is-projective-Cardinal (l1 ⊔ l2) Y →
    is-discrete-Cardinal Y →
    merely-decidable-∃-Cardinal (l1 ⊔ l2) Y →
    leq-Cardinal X Y →
    le-indexed-Cardinal X Y ↔ le-Cardinal X Y
  le-iff-le-indexed-Cardinal lem =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ X Y →
        set-Prop
          ( function-Prop
            ( merely-decidable-∃-Cardinal l2 X)
            ( function-Prop
              ( is-projective-Cardinal (l1 ⊔ l2) Y)
              ( function-Prop
                ( is-discrete-Cardinal Y)
                ( function-Prop
                  ( merely-decidable-∃-Cardinal (l1 ⊔ l2) Y)
                  ( function-Prop
                    ( leq-Cardinal X Y)
                    ( iff-Prop
                      ( le-indexed-prop-Cardinal X Y)
                      ( le-prop-Cardinal X Y))))))))
      ( λ X Y merely-Σ-X is-projective-Y is-discrete-Y merely-Σ-Y →
        le-iff-le-indexed-cardinality
          ( lem)
          ( X)
          ( Y)
          ( inv-unit-merely-decidable-∃-cardinality X merely-Σ-X)
          ( inv-unit-is-projective-cardinality Y is-projective-Y)
          ( inv-unit-is-discrete-cardinality Y is-discrete-Y)
          ( inv-unit-merely-decidable-∃-cardinality Y merely-Σ-Y))

  le-iff-le-indexed-Cardinal-WLPO :
    (wlpo : level-WLPO (l1 ⊔ l2)) →
    (X : Cardinal l1) (Y : Cardinal l2) →
    is-discrete-Cardinal X →
    merely-decidable-∃-Cardinal l2 X →
    is-projective-Cardinal (l1 ⊔ l2) Y →
    is-discrete-Cardinal Y →
    merely-decidable-∃-Cardinal (l1 ⊔ l2) Y →
    leq-Cardinal X Y →
    le-indexed-Cardinal X Y ↔ le-Cardinal X Y
  le-iff-le-indexed-Cardinal-WLPO wlpo =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ X Y →
        set-Prop
          ( function-Prop
            ( is-discrete-Cardinal X)
            ( function-Prop
              ( merely-decidable-∃-Cardinal l2 X)
              ( function-Prop
                ( is-projective-Cardinal (l1 ⊔ l2) Y)
                ( function-Prop
                  ( is-discrete-Cardinal Y)
                  ( function-Prop
                    ( merely-decidable-∃-Cardinal (l1 ⊔ l2) Y)
                    ( function-Prop
                      ( leq-Cardinal X Y)
                      ( iff-Prop
                        ( le-indexed-prop-Cardinal X Y)
                        ( le-prop-Cardinal X Y)))))))))
      ( λ X Y
          is-discrete-X merely-Σ-X
          is-projective-Y is-discrete-Y merely-Σ-Y →
        le-iff-le-indexed-cardinality-WLPO
          ( wlpo)
          ( X)
          ( Y)
          ( inv-unit-is-discrete-cardinality X is-discrete-X)
          ( inv-unit-merely-decidable-∃-cardinality X merely-Σ-X)
          ( inv-unit-is-projective-cardinality Y is-projective-Y)
          ( inv-unit-is-discrete-cardinality Y is-discrete-Y)
          ( inv-unit-merely-decidable-∃-cardinality Y merely-Σ-Y))
```
