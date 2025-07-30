# The axiom of countable choice

```agda
module foundation.axiom-of-countable-choice where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.axiom-of-choice
open import foundation.axiom-of-dependent-choice
open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.maybe
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import set-theory.countable-sets

open import univalent-combinatorics.classical-finite-types
```

</details>

## Idea

The
{{#concept "axiom of countable choice" WD="axiom of countable choice" WDID=Q1000116 Agda=ACω}}
asserts that for every family of [inhabited](foundation.inhabited-types.md)
types `B` indexed by the
[natural numbers](elementary-number-theory.natural-numbers.md) `ℕ`, the type of
sections of that family `(n : ℕ) → B n` is inhabited.

## Definition

```agda
level-ACω : (l : Level) → UU (lsuc l)
level-ACω l =
  (f : ℕ → Set l) (inhabited-f : (n : ℕ) → is-inhabited (type-Set (f n))) →
  is-inhabited ((n : ℕ) → type-Set (f n))

ACω : UUω
ACω = {l : Level} → level-ACω l
```

## Properties

### The axiom of countable choice implies choice for countable sets with decidable equality

```agda
module _
  {l : Level} (X : Set l)
  (countable-X : is-countable X)
  (decidable-equality-X : has-decidable-equality (type-Set X))
  where

  choice-countable-decidable-set-ACω :
    {l2 : Level} → ACω →
    (F : type-Set X → Set l2) →
    (inhabited-F : (x : type-Set X) → is-inhabited (type-Set (F x))) →
    is-inhabited ((x : type-Set X) → type-Set (F x))
  choice-countable-decidable-set-ACω {l2} acω F inhabited-F =
    let
      open
        do-syntax-trunc-Prop
          ( is-inhabited-Prop ((x : type-Set X) → type-Set (F x)))
      F' : Maybe (type-Set X) → Set l2
      F' = rec-coproduct F (λ _ → raise-Set l2 unit-Set)
      inhabited-F' : (x : Maybe (type-Set X)) → is-inhabited (type-Set (F' x))
      inhabited-F' = λ where
        (inl x) → inhabited-F x
        (inr star) → unit-trunc-Prop (map-raise star)
    in do
      e ← countable-X
      g ← acω (F' ∘ map-enumeration X e) (inhabited-F' ∘ map-enumeration X e)
      unit-trunc-Prop
        ( λ x →
          let
            ( n , en=unit-x , _) =
              minimal-preimage-enumerated-decidable-Set
                ( X)
                ( e)
                ( decidable-equality-X)
                ( x)
          in map-eq (ap (type-Set ∘ F') en=unit-x) (g n))
```

### The axiom of choice implies the axiom of countable choice

```agda
level-ACω-level-AC0 : {l : Level} → level-AC0 lzero l → level-ACω l
level-ACω-level-AC0 ac0 f inhabited-f =
  ac0
    ( ℕ-Set)
    ( λ n → type-Set (f n))
    ( λ n → inhabited-f n)

ACω-AC0 : AC0 → ACω
ACω-AC0 ac0 = level-ACω-level-AC0 ac0
```

### The axiom of dependent choice implies the axiom of countable choice

```agda
level-ACω-level-ADC : {l : Level} → level-ADC l lzero → level-ACω l
level-ACω-level-ADC {l} adc f inhabited-f =
  do
    (g , r-gn-g⟨n+1⟩) ←
      adc (A , is-set-A) (unit-trunc-Prop (0 , λ ())) R entire-R
    let
      dom-g : (m : ℕ) → m ≤-ℕ pr1 (g m)
      dom-g =
        ind-ℕ
          ( leq-zero-ℕ (pr1 (g 0)))
          ( λ m m≤gn → tr (leq-ℕ (succ-ℕ m)) (r-gn-g⟨n+1⟩ m) m≤gn)
      h : (m : ℕ) (k : classical-Fin m) → type-Set (f (pr1 k))
      h =
        λ m (k , k<m) →
          pr2 (g m) (k , concatenate-le-leq-ℕ {k} {m} {pr1 (g m)} k<m (dom-g m))
    unit-trunc-Prop (λ n → h (succ-ℕ n) (n , succ-le-ℕ n))
  where
    open
      do-syntax-trunc-Prop
        ( is-inhabited-Prop ((n : ℕ) → type-Set (f n)))
    A : UU l
    A =
      Σ ℕ
        ( λ n →
          (k : classical-Fin n) →
          type-Set (f (nat-classical-Fin n k)))
    is-set-A : is-set A
    is-set-A = is-set-Σ is-set-ℕ (λ _ → is-set-Π (pr2 ∘ f ∘ pr1))
    R : Relation lzero A
    R (m , _) (n , _) = succ-ℕ m ＝ n
    entire-R : is-entire-Relation R
    entire-R (n , f<n) =
      rec-trunc-Prop
        ( is-inhabited-Prop (Σ A (R (n , f<n))))
        ( λ fn →
          unit-trunc-Prop
            ( ( succ-ℕ n ,
                λ (k , k<sn) →
                  rec-coproduct
                    ( λ k<n → f<n (k , k<n))
                    ( λ n≤k →
                      map-eq
                        ( ap
                          ( type-Set ∘ f)
                          ( antisymmetric-leq-ℕ n k
                            ( n≤k)
                            ( leq-le-succ-ℕ k n k<sn)))
                        ( fn))
                    ( decide-le-leq-ℕ k n)) ,
              refl))
        ( inhabited-f n)
```

## See also

- [The axiom of choice](foundation.axiom-of-choice.md)
- [The axiom of dependent choice](foundation.axiom-of-dependent-choice.md)
