# Finiteness of the type of connected components

```agda
module univalent-combinatorics.finitely-many-connected-components where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.0-connected-types
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fiber-inclusions
open import foundation.function-types
open import foundation.functoriality-set-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.mere-equality
open import foundation.mere-equivalences
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.image-of-maps
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A type is said to have
{{#concept "finitely many connected components" Agda=has-finitely-many-components}}
if its [set truncation](foundation.set-truncations.md) is a
[finite type](univalent-combinatorics.finite-types.md).

## Definitions

### Types with finitely many connected components

```agda
has-finitely-many-connected-components-Prop : {l : Level} → UU l → Prop l
has-finitely-many-connected-components-Prop A =
  is-finite-Prop (type-trunc-Set A)

has-finitely-many-connected-components : {l : Level} → UU l → UU l
has-finitely-many-connected-components A =
  type-Prop (has-finitely-many-connected-components-Prop A)

number-of-connected-components :
  {l : Level} {X : UU l} → has-finitely-many-connected-components X → ℕ
number-of-connected-components H = number-of-elements-is-finite H

mere-equiv-number-of-connected-components :
  {l : Level} {X : UU l} (H : has-finitely-many-connected-components X) →
  mere-equiv
    ( Fin (number-of-connected-components H))
    ( type-trunc-Set X)
mere-equiv-number-of-connected-components H =
  mere-equiv-is-finite H
```

### Types with a finite type of connected components of a specified cardinality

```agda
has-cardinality-components-Prop : {l : Level} (k : ℕ) → UU l → Prop l
has-cardinality-components-Prop k A =
  has-cardinality-Prop k (type-trunc-Set A)

has-cardinality-components : {l : Level} (k : ℕ) → UU l → UU l
has-cardinality-components k A =
  type-Prop (has-cardinality-components-Prop k A)
```

## Properties

### Having finitely many connected components is invariant under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  has-finitely-many-connected-components-equiv :
    has-finitely-many-connected-components A → has-finitely-many-connected-components B
  has-finitely-many-connected-components-equiv =
    is-finite-equiv (equiv-trunc-Set e)

  has-finitely-many-connected-components-equiv' :
    has-finitely-many-connected-components B → has-finitely-many-connected-components A
  has-finitely-many-connected-components-equiv' =
    is-finite-equiv' (equiv-trunc-Set e)
```

### Any 0-connected type has finitely many connected components

```agda
has-finitely-many-connected-components-is-0-connected :
  {l : Level} {A : UU l} →
  is-0-connected A → has-finitely-many-connected-components A
has-finitely-many-connected-components-is-0-connected = is-finite-is-contr
```

### Sets with finitely many connected components are finite

```agda
is-finite-has-finitely-many-connected-components :
  {l : Level} {A : UU l} →
  is-set A → has-finitely-many-connected-components A → is-finite A
is-finite-has-finitely-many-connected-components H =
  is-finite-equiv' (equiv-unit-trunc-Set (_ , H))
```

### Dependent sums of types with finitely many connected components

The total space of a family of types with finitely many connected components has
finitely many connected components when the base is `0`-connected and its based
[loop spaces](synthetic-homotopy-theory.loop-spaces.md) have finitely many
connected components.

```agda
has-finitely-many-connected-components-Σ-is-0-connected :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-0-connected A →
  ((a : A) → has-finitely-many-connected-components (a ＝ a)) →
  ((x : A) → has-finitely-many-connected-components (B x)) →
  has-finitely-many-connected-components (Σ A B)
has-finitely-many-connected-components-Σ-is-0-connected {A = A} {B} C H K =
  apply-universal-property-trunc-Prop
    ( is-inhabited-is-0-connected C)
    ( has-finitely-many-connected-components-Prop (Σ A B))
    ( α)
  where
  α : A → has-finitely-many-connected-components (Σ A B)
  α a =
    is-finite-codomain
      ( K a)
      ( is-surjective-map-trunc-Set
        ( fiber-inclusion B a)
        ( is-surjective-fiber-inclusion C a))
      ( apply-dependent-universal-property-trunc-Set'
        ( λ x →
          set-Prop
            ( Π-Prop
              ( type-trunc-Set (Σ A B))
              ( λ y → is-decidable-Prop (Id-Prop (trunc-Set (Σ A B)) x y))))
        ( β))
    where
    β :
      (x : Σ A B) (v : type-trunc-Set (Σ A B)) →
      is-decidable (unit-trunc-Set x ＝ v)
    β (x , y) =
      apply-dependent-universal-property-trunc-Set'
        ( λ u →
          set-Prop
            ( is-decidable-Prop
              ( Id-Prop (trunc-Set (Σ A B)) (unit-trunc-Set (x , y)) u)))
        ( γ)
      where
      γ :
        (v : Σ A B) →
        is-decidable ((unit-trunc-Set (x , y)) ＝ (unit-trunc-Set v))
      γ (x' , y') =
        is-decidable-equiv
          ( is-effective-unit-trunc-Set
            ( Σ A B)
            ( x , y)
            ( x' , y'))
          ( apply-universal-property-trunc-Prop
            ( mere-eq-is-0-connected C a x)
            ( is-decidable-Prop
              ( mere-eq-Prop (x , y) (x' , y')))
              ( δ))
        where
        δ : a ＝ x → is-decidable (mere-eq (x , y) (x' , y'))
        δ refl =
          apply-universal-property-trunc-Prop
            ( mere-eq-is-0-connected C a x')
            ( is-decidable-Prop
              ( mere-eq-Prop (a , y) (x' , y')))
            ( ε)
          where
          ε : a ＝ x' → is-decidable (mere-eq (x , y) (x' , y'))
          ε refl =
            is-decidable-equiv e
              ( is-decidable-type-trunc-Prop-is-finite
                ( is-finite-Σ
                  ( H a)
                  ( λ ω → is-finite-is-decidable-Prop (P ω) (d ω))))
            where
            ℙ :
              is-contr
                ( Σ ( hom-Set (trunc-Set (a ＝ a)) (Prop-Set _))
                    ( λ h →
                      ( λ a₁ → h (unit-trunc-Set a₁)) ~
                      ( λ ω₁ →
                        trunc-Prop (dependent-identification B ω₁ y y'))))
            ℙ =
              universal-property-trunc-Set
                ( a ＝ a)
                ( Prop-Set _)
                ( λ ω → trunc-Prop (dependent-identification B ω y y'))

            P : type-trunc-Set (Id a a) → Prop _
            P = pr1 (center ℙ)

            compute-P :
              (ω : a ＝ a) →
              type-Prop (P (unit-trunc-Set ω)) ≃
              type-trunc-Prop (dependent-identification B ω y y')
            compute-P ω = equiv-eq (ap pr1 (pr2 (center ℙ) ω))

            d : (t : type-trunc-Set (a ＝ a)) → is-decidable (type-Prop (P t))
            d =
              apply-dependent-universal-property-trunc-Set'
                ( λ t → set-Prop (is-decidable-Prop (P t)))
                ( λ ω →
                  is-decidable-equiv'
                    ( inv-equiv (compute-P ω))
                    ( is-decidable-equiv'
                      ( is-effective-unit-trunc-Set (B a) (tr B ω y) y')
                      ( has-decidable-equality-is-finite
                        ( K a)
                        ( unit-trunc-Set (tr B ω y))
                        ( unit-trunc-Set y'))))

            f : type-hom-Prop
                ( trunc-Prop (Σ (type-trunc-Set (Id a a)) (type-Prop ∘ P)))
                ( mere-eq-Prop {A = Σ A B} (a , y) (a , y'))
            f t =
              apply-universal-property-trunc-Prop t
                ( mere-eq-Prop (a , y) (a , y'))
                  λ (u , v) →
                  apply-dependent-universal-property-trunc-Set'
                    ( λ u' →
                      hom-set-Set
                        ( set-Prop (P u'))
                        ( set-Prop
                          ( mere-eq-Prop (a , y) (a , y'))))
                    ( λ ω v' →
                      apply-universal-property-trunc-Prop
                        ( map-equiv (compute-P ω) v')
                        ( mere-eq-Prop (a , y) (a , y'))
                        ( λ p → unit-trunc-Prop (eq-pair-Σ ω p)))
                    ( u)
                    ( v)
            e :
              mere-eq {A = Σ A B} (a , y) (a , y') ≃
              type-trunc-Prop (Σ (type-trunc-Set (Id a a)) (type-Prop ∘ P))
            e =
              equiv-iff
                ( mere-eq-Prop (a , y) (a , y'))
                ( trunc-Prop (Σ (type-trunc-Set (a ＝ a)) (type-Prop ∘ P)))
                ( λ t →
                  apply-universal-property-trunc-Prop t
                    ( trunc-Prop _)
                    ( ( λ (ω , r) →
                        unit-trunc-Prop
                          ( ( unit-trunc-Set ω) ,
                            ( map-inv-equiv
                              ( compute-P ω)
                              ( unit-trunc-Prop r)))) ∘
                      ( pair-eq-Σ)))
                ( f)
```

## See also

- [Kuratowsky finite sets](univalent-combinatorics.kuratowsky-finite-sets.md)
