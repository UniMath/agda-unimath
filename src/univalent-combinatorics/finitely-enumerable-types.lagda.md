# Finitely enumerable types

```agda
module univalent-combinatorics.finitely-enumerable-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-booleans
open import foundation.type-arithmetic-coproduct-types
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-decidable-subtypes
open import univalent-combinatorics.counting-dependent-pair-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.surjective-maps
```

</details>

## Idea

A type `X` is
{{#concept "finitely enumerable" disambiguation="type" Agda=is-finitely-enumerable}}
if there [exists](foundation.existential-quantification.md) an `n : ℕ` and a
[surjection](foundation.surjective-maps.md) from `Fin n → X`.

## Definition

```agda
module _
  {l : Level} (X : UU l)
  where

  finite-enumeration : UU l
  finite-enumeration = Σ ℕ (λ n → Fin n ↠ X)

  is-finitely-enumerable-prop : Prop l
  is-finitely-enumerable-prop = trunc-Prop finite-enumeration

  is-finitely-enumerable : UU l
  is-finitely-enumerable = type-Prop is-finitely-enumerable-prop

Finitely-Enumerable-Type : (l : Level) → UU (lsuc l)
Finitely-Enumerable-Type l = type-subtype (is-finitely-enumerable-prop {l})

module _
  {l : Level} (X : Finitely-Enumerable-Type l)
  where

  type-Finitely-Enumerable-Type : UU l
  type-Finitely-Enumerable-Type = pr1 X

  is-finitely-enumerable-type-Finitely-Enumerable-Type :
    is-finitely-enumerable type-Finitely-Enumerable-Type
  is-finitely-enumerable-type-Finitely-Enumerable-Type = pr2 X
```

## Properties

### Finitely enumerable types are closed under equivalences

```agda
finite-enumeration-equiv :
  {l1 : Level} {X : UU l1} → finite-enumeration X →
  {l2 : Level} {Y : UU l2} → X ≃ Y → finite-enumeration Y
finite-enumeration-equiv (n , Fin-n↠X) X≃Y =
  ( n ,
    map-equiv X≃Y ∘ map-surjection Fin-n↠X ,
    is-surjective-left-comp-equiv X≃Y (is-surjective-map-surjection Fin-n↠X))
```

### Finitely enumerable types with decidable equality are finite

```agda
count-finite-enumeration-discrete :
  {l : Level} {X : UU l} →
  has-decidable-equality X → finite-enumeration X → count X
count-finite-enumeration-discrete D (n , Fin-n↠X) =
  count-surjection-has-decidable-equality n D Fin-n↠X

is-finite-is-finitely-enumerable-discrete :
  {l : Level} {X : UU l} →
  has-decidable-equality X → is-finitely-enumerable X → is-finite X
is-finite-is-finitely-enumerable-discrete D eX =
  ∃-surjection-has-decidable-equality-if-is-finite (D , eX)
```

### Finite types are finitely enumerable

```agda
finite-enumeration-count :
  {l : Level} {X : UU l} → count X → finite-enumeration X
finite-enumeration-count (n , Fin-n≃X) = (n , surjection-equiv Fin-n≃X)

is-finitely-enumerable-is-finite :
  {l : Level} {X : UU l} → is-finite X → is-finitely-enumerable X
is-finitely-enumerable-is-finite {X = X} =
  rec-trunc-Prop
    ( is-finitely-enumerable-prop X)
    ( unit-trunc-Prop ∘ finite-enumeration-count)

is-finitely-enumerable-type-Finite-Type :
  {l : Level} (X : Finite-Type l) → is-finitely-enumerable (type-Finite-Type X)
is-finitely-enumerable-type-Finite-Type (X , is-finite-X) =
  is-finitely-enumerable-is-finite is-finite-X

finitely-enumerable-type-Finite-Type :
  {l : Level} → Finite-Type l → Finitely-Enumerable-Type l
finitely-enumerable-type-Finite-Type (X , is-finite-X) =
  (X , is-finitely-enumerable-is-finite is-finite-X)
```

### Finitely enumerable types are closed under dependent sums

```agda
abstract
  finite-enumeration-Σ :
    {l1 l2 : Level} {A : UU l1} → finite-enumeration A →
    (B : A → UU l2) → ((a : A) → finite-enumeration (B a)) →
    finite-enumeration (Σ A B)
  finite-enumeration-Σ {A = A} eA@(nA , Fin-nA↠A) B eB =
    let
      (n , Fin-n≃ΣAn) =
        count-Σ
          ( count-Fin nA)
          ( count-Fin ∘ pr1 ∘ eB ∘ map-surjection Fin-nA↠A)
      map-surj =
        ind-Σ
          ( λ iA i-nBa →
            ( map-surjection Fin-nA↠A iA ,
              map-surjection (pr2 (eB (map-surjection Fin-nA↠A iA))) i-nBa))
      is-surjective-map-surj =
        λ (a , b) →
          let open do-syntax-trunc-Prop (trunc-Prop (fiber map-surj (a , b)))
          in do
            (ia , refl) ← is-surjective-map-surjection Fin-nA↠A a
            (ib , refl) ←
              is-surjective-map-surjection (pr2 (eB a)) b
            intro-exists (ia , ib) refl
    in
      ( n ,
        map-surj ∘ map-equiv Fin-n≃ΣAn ,
        is-surjective-right-comp-equiv is-surjective-map-surj Fin-n≃ΣAn)
```

### `X` and `Y` are finitely enumerable if and only if `X + Y` is finitely enumerable

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  abstract
    finite-enumeration-left-summand :
      finite-enumeration (X + Y) → finite-enumeration X
    finite-enumeration-left-summand (n+ , Fin-n+↠X+Y) =
      let
        (nₗ , Fin-nₗ≃n+-inl) =
          count-decidable-subtype
            ( λ iₙ₊ → is-left-Decidable-Prop (map-surjection Fin-n+↠X+Y iₙ₊))
            ( count-Fin n+)
        map-surj =
          ind-Σ
            ( λ iₙ₊ is-left-f-iₙ₊ →
              left-is-left (map-surjection Fin-n+↠X+Y iₙ₊) (is-left-f-iₙ₊))
        helper :
          (x? : X + Y) (x' : X) → (x? ＝ inl x') → (L : is-left x?) →
          left-is-left x? L ＝ x'
        helper = λ where
          (inl _) _ x?=inl-x' _ → is-injective-inl x?=inl-x'
        is-surjective-map-surj x =
          let open do-syntax-trunc-Prop (trunc-Prop (fiber map-surj x))
          in do
            (iₙ₊ , fiₙ₊=inl-x) ← is-surjective-map-surjection Fin-n+↠X+Y (inl x)
            let is-left-fiₙ₊ = inv-tr is-left fiₙ₊=inl-x star
            intro-exists
              ( iₙ₊ , is-left-fiₙ₊)
              ( helper _ _ fiₙ₊=inl-x is-left-fiₙ₊)
      in
        ( nₗ ,
          map-surj ∘ map-equiv Fin-nₗ≃n+-inl ,
          is-surjective-right-comp-equiv is-surjective-map-surj Fin-nₗ≃n+-inl)

abstract
  finite-enumeration-right-summand :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    finite-enumeration (X + Y) → finite-enumeration Y
  finite-enumeration-right-summand eX+Y =
    finite-enumeration-left-summand
      ( finite-enumeration-equiv eX+Y (commutative-coproduct _ _))

finite-enumeration-coproduct :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  finite-enumeration X → finite-enumeration Y → finite-enumeration (X + Y)
finite-enumeration-coproduct {l1} {l2} {X} {Y} eX eY =
  let
    F = rec-bool (raise l2 X) (raise l1 Y)
    eF : (b : bool) → finite-enumeration (F b)
    eF = λ where
      false → finite-enumeration-equiv eY (compute-raise l1 Y)
      true → finite-enumeration-equiv eX (compute-raise l2 X)
  in
    finite-enumeration-equiv
      ( finite-enumeration-Σ
        ( finite-enumeration-count (2 , equiv-bool-Fin-2))
        ( F)
        ( eF))
      ( equiv-coproduct (inv-compute-raise l2 X) (inv-compute-raise l1 Y) ∘e
        equiv-Σ-bool-coproduct F)

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  coproduct-is-finitely-enumerable-iff-each-finitely-enumerable :
    is-finitely-enumerable (X + Y) ↔
    is-finitely-enumerable X × is-finitely-enumerable Y
  pr1 coproduct-is-finitely-enumerable-iff-each-finitely-enumerable =
    rec-trunc-Prop
      ( is-finitely-enumerable-prop X ∧ is-finitely-enumerable-prop Y)
      ( λ eX+Y →
        ( unit-trunc-Prop (finite-enumeration-left-summand eX+Y) ,
          unit-trunc-Prop (finite-enumeration-right-summand eX+Y)))
  pr2 coproduct-is-finitely-enumerable-iff-each-finitely-enumerable (eX , eY) =
    let open do-syntax-trunc-Prop (is-finitely-enumerable-prop (X + Y))
    in do
      enum-X ← eX
      enum-Y ← eY
      unit-trunc-Prop (finite-enumeration-coproduct enum-X enum-Y)
```

### Finitely enumerable types are closed under Cartesian products

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  finite-enumeration-product :
    finite-enumeration X → finite-enumeration Y → finite-enumeration (X × Y)
  finite-enumeration-product (nX , Fin-nX↠X) (nY , Fin-nY↠Y) =
    let
      surj-map : (Fin nX × Fin nY) → X × Y
      surj-map =
        map-product (map-surjection Fin-nX↠X) (map-surjection Fin-nY↠Y)
      is-surjective-surj-map : is-surjective surj-map
      is-surjective-surj-map =
        λ (x , y) →
          let open do-syntax-trunc-Prop (trunc-Prop (fiber surj-map (x , y)))
          in do
            (ix , fix=x) ← is-surjective-map-surjection Fin-nX↠X x
            (iy , fiy=y) ← is-surjective-map-surjection Fin-nY↠Y y
            intro-exists (ix , iy) (eq-pair fix=x fiy=y)
    in
      ( nX *ℕ nY ,
        surj-map ∘ map-inv-equiv (product-Fin nX nY) ,
        is-surjective-right-comp-equiv
          ( is-surjective-surj-map)
          ( inv-equiv (product-Fin nX nY)))

  is-finitely-enumerable-product :
    is-finitely-enumerable X → is-finitely-enumerable Y →
    is-finitely-enumerable (X × Y)
  is-finitely-enumerable-product eX eY =
    let open do-syntax-trunc-Prop (is-finitely-enumerable-prop (X × Y))
    in do
      ex ← eX
      ey ← eY
      unit-trunc-Prop (finite-enumeration-product ex ey)

product-Finitely-Enumerable-Type :
  {l1 l2 : Level}
  (X : Finitely-Enumerable-Type l1)
  (Y : Finitely-Enumerable-Type l2) →
  Finitely-Enumerable-Type (l1 ⊔ l2)
product-Finitely-Enumerable-Type (X , eX) (Y , eY) =
  (X × Y , is-finitely-enumerable-product eX eY)
```

## See also

- A [Kuratowski finite set](univalent-combinatorics.kuratowski-finite-sets.md)
  is precisely a finitely enumerable [set](foundation.sets.md).
