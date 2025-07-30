# The axiom of countable choice

```agda
module foundation.axiom-of-countable-choice where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.addition-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.axiom-of-choice
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.axiom-of-dependent-choice
open import foundation.function-types
open import univalent-combinatorics.classical-finite-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.binary-relations
open import foundation.maybe
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import set-theory.countable-sets
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
  (f : ℕ → Inhabited-Type l) →
  is-inhabited ((n : ℕ) → type-Inhabited-Type (f n))

ACω : UUω
ACω = {l : Level} → level-ACω l
```

## Properties

### The axiom of countable choice implies choice for countable sets with decidable equality

```agda
module _
  {l : Level} (X : Set l)
  (ic : is-countable X) (hde : has-decidable-equality (type-Set X))
  where

  choice-countable-decidable-set-ACω :
    {l2 : Level} → ACω → (F : type-Set X → Inhabited-Type l2) →
    is-inhabited ((x : type-Set X) → type-Inhabited-Type (F x))
  choice-countable-decidable-set-ACω {l2} acω F =
    let
      open
        do-syntax-trunc-Prop
          ( is-inhabited-Prop ((x : type-Set X) → type-Inhabited-Type (F x)))
      F' : Maybe (type-Set X) → Inhabited-Type l2
      F' =
        rec-coproduct
          ( F)
          ( λ star → (raise l2 unit , unit-trunc-Prop (map-raise star)))
    in do
      e ← ic
      g ← acω (F' ∘ map-enumeration X e)
      unit-trunc-Prop
        ( λ x →
          let
            ( n , en=unit-x , _) =
              minimal-preimage-enumerated-decidable-Set X e hde x
          in map-eq (ap (type-Inhabited-Type ∘ F') en=unit-x) (g n))
```

### The axiom of choice implies the axiom of countable choice

```agda
level-ACω-level-AC0 : {l : Level} → level-AC0 lzero l → level-ACω l
level-ACω-level-AC0 ac0 f =
  ac0
    ( ℕ-Set)
    ( λ n → type-Inhabited-Type (f n))
    ( λ n → is-inhabited-type-Inhabited-Type (f n))

ACω-AC0 : AC0 → ACω
ACω-AC0 ac0 = level-ACω-level-AC0 ac0
```

### The axiom of dependent choice implies the axiom of countable choice

```agda
level-ACω-level-ADC : {l : Level} → level-ADC l lzero → level-ACω l
level-ACω-level-ADC {l} adc f =
  do
    (g , r-gn-g⟨n+1⟩) ← adc A (unit-trunc-Prop (0 , λ ())) R entire-R
    let
      (n₀ , gn₀) = g zero-ℕ
      dom-g : (m : ℕ) → pr1 (g m) ＝ n₀ +ℕ m
      dom-g = ind-ℕ refl (λ m claim-m → inv (r-gn-g⟨n+1⟩ m) ∙ ap succ-ℕ claim-m)
      h :
        (m : ℕ) (k : classical-Fin (n₀ +ℕ m)) →
        type-Inhabited-Type (f (pr1 k))
      h m =
        map-eq
          ( ap
            ( λ x → (k : classical-Fin x) → type-Inhabited-Type (f (pr1 k)))
            ( dom-g m))
          ( pr2 (g m))
    unit-trunc-Prop
      ( λ n →
        rec-coproduct
          ( λ n<n₀ → gn₀ (n , n<n₀))
          ( λ n₀≤n →
            let
              (m , m+n₀=n) = subtraction-leq-ℕ n₀ n n₀≤n
            in
              map-eq
                ( ap (pr1 ∘ f) (commutative-add-ℕ n₀ m ∙ m+n₀=n))
                ( h (succ-ℕ m) (n₀ +ℕ m , succ-le-ℕ (n₀ +ℕ m))))
          ( decide-le-leq-ℕ n n₀))
  where
    open
      do-syntax-trunc-Prop
        ( is-inhabited-Prop ((n : ℕ) → type-Inhabited-Type (f n)))
    A : UU l
    A =
      Σ ℕ
        ( λ n →
          (k : classical-Fin n) →
          type-Inhabited-Type (f (nat-classical-Fin n k)))
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
                          ( type-Inhabited-Type ∘ f)
                          ( antisymmetric-leq-ℕ n k
                            ( n≤k)
                            ( leq-le-succ-ℕ k n k<sn)))
                        ( fn))
                    ( decide-le-leq-ℕ k n)) ,
              refl))
        ( is-inhabited-type-Inhabited-Type (f n))
```
