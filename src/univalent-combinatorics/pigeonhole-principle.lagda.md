# The pigeonhole principle

```agda
module univalent-combinatorics.pigeonhole-principle where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-types
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.well-ordering-principle-standard-finite-types

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negation
open import foundation.pairs-of-distinct-elements
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.repetitions
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-dependent-function-types
open import univalent-combinatorics.decidable-propositions
open import univalent-combinatorics.embeddings-standard-finite-types
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

If `f : X → Y` is an injective map between finite types `X` and `Y` with `k` and
`l` elements, then `k ≤ l`. Conversely, if `l < k`, then no map `f : X → Y` is
injective.

## Theorems

### The pigeonhole principle for the standard finite types

```agda
abstract
  leq-emb-Fin :
    (k l : ℕ) → Fin k ↪ Fin l → k ≤-ℕ l
  leq-emb-Fin zero-ℕ zero-ℕ f = refl-leq-ℕ zero-ℕ
  leq-emb-Fin (succ-ℕ k) zero-ℕ f = ex-falso (map-emb f (inr star))
  leq-emb-Fin zero-ℕ (succ-ℕ l) f = leq-zero-ℕ (succ-ℕ l)
  leq-emb-Fin (succ-ℕ k) (succ-ℕ l) f = leq-emb-Fin k l (reduce-emb-Fin k l f)

abstract
  leq-is-emb-Fin :
    (k l : ℕ) {f : Fin k → Fin l} → is-emb f → k ≤-ℕ l
  leq-is-emb-Fin k l {f = f} H = leq-emb-Fin k l (pair f H)

abstract
  leq-is-injective-Fin :
    (k l : ℕ) {f : Fin k → Fin l} → is-injective f → k ≤-ℕ l
  leq-is-injective-Fin k l H =
    leq-is-emb-Fin k l (is-emb-is-injective (is-set-Fin l) H)

abstract
  is-not-emb-le-Fin :
    (k l : ℕ) (f : Fin k → Fin l) → le-ℕ l k → ¬ (is-emb f)
  is-not-emb-le-Fin k l f p =
    map-neg (leq-is-emb-Fin k l) (contradiction-le-ℕ l k p)

abstract
  is-not-injective-le-Fin :
    (k l : ℕ) (f : Fin k → Fin l) → le-ℕ l k → ¬ (is-injective f)
  is-not-injective-le-Fin k l f p =
    map-neg (is-emb-is-injective (is-set-Fin l)) (is-not-emb-le-Fin k l f p)

abstract
  is-not-injective-map-Fin-succ-Fin :
    (k : ℕ) (f : Fin (succ-ℕ k) → Fin k) → ¬ (is-injective f)
  is-not-injective-map-Fin-succ-Fin k f =
    is-not-injective-le-Fin (succ-ℕ k) k f (le-succ-ℕ {k})

abstract
  no-embedding-ℕ-Fin :
    (k : ℕ) → ¬ (ℕ ↪ Fin k)
  no-embedding-ℕ-Fin k e =
    contradiction-leq-ℕ k k
      ( refl-leq-ℕ k)
      ( leq-emb-Fin (succ-ℕ k) k (comp-emb e (emb-nat-Fin (succ-ℕ k))))
```

### For any `f : Fin k → Fin l`, where `l < k`, we construct a pair of distinct elements of `Fin k` on which `f` assumes the same value

```agda
module _
  (k l : ℕ) (f : Fin k → Fin l) (p : le-ℕ l k)
  where

  abstract
    repetition-le-Fin : repetition f
    repetition-le-Fin =
      pair (pair x (pair y (pr2 w))) (pr1 w)
      where
      u : Σ (Fin k) (λ x → ¬ ((y : Fin k) → Id (f x) (f y) → Id x y))
      u =
        exists-not-not-forall-Fin k
          ( λ x →
            is-decidable-Π-Fin k
              ( λ y →
                is-decidable-function-type
                  ( has-decidable-equality-Fin l (f x) (f y))
                  ( has-decidable-equality-Fin k x y)))
          ( λ q → is-not-injective-le-Fin k l f p (λ {x} {y} r → q x y r))
      x : Fin k
      x = pr1 u
      H : ¬ ((y : Fin k) → Id (f x) (f y) → Id x y)
      H = pr2 u
      v : Σ (Fin k) (λ y → ¬ (Id (f x) (f y) → Id x y))
      v = exists-not-not-forall-Fin k
          ( λ y →
            is-decidable-function-type
              ( has-decidable-equality-Fin l (f x) (f y))
              ( has-decidable-equality-Fin k x y))
          ( H)
      y : Fin k
      y = pr1 v
      K : ¬ (Id (f x) (f y) → Id x y)
      K = pr2 v
      w : Id (f x) (f y) × ¬ (Id x y)
      w = exists-not-not-forall-count
          ( λ _ → Id x y)
          ( λ _ →
            has-decidable-equality-Fin k x y)
          ( count-is-decidable-is-prop
            ( is-set-Fin l (f x) (f y))
            ( has-decidable-equality-Fin l (f x) (f y)))
          ( K)

  pair-of-distinct-elements-repetition-le-Fin :
    pair-of-distinct-elements (Fin k)
  pair-of-distinct-elements-repetition-le-Fin = pr1 repetition-le-Fin

  fst-repetition-le-Fin : Fin k
  fst-repetition-le-Fin =
    fst-pair-of-distinct-elements pair-of-distinct-elements-repetition-le-Fin

  snd-repetition-le-Fin : Fin k
  snd-repetition-le-Fin =
    snd-pair-of-distinct-elements pair-of-distinct-elements-repetition-le-Fin

  distinction-repetition-le-Fin :
    ¬ (Id fst-repetition-le-Fin snd-repetition-le-Fin)
  distinction-repetition-le-Fin =
    distinction-pair-of-distinct-elements
      pair-of-distinct-elements-repetition-le-Fin

  is-repetition-pair-of-distinct-elements-repetition-le-Fin :
    is-repetition-pair-of-distinct-elements f
      pair-of-distinct-elements-repetition-le-Fin
  is-repetition-pair-of-distinct-elements-repetition-le-Fin =
    is-repetition-pair-of-distinct-elements-repetition f repetition-le-Fin
```

### The pigeonhole principle for types equipped with a counting

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (eA : count A) (eB : count B)
  where

  abstract
    leq-emb-count :
      (A ↪ B) → (number-of-elements-count eA) ≤-ℕ (number-of-elements-count eB)
    leq-emb-count f =
      leq-emb-Fin
        ( number-of-elements-count eA)
        ( number-of-elements-count eB)
        ( comp-emb
          ( comp-emb (emb-equiv (inv-equiv-count eB)) f)
          ( emb-equiv (equiv-count eA)))

  abstract
    leq-is-emb-count :
      {f : A → B} → is-emb f →
      (number-of-elements-count eA) ≤-ℕ (number-of-elements-count eB)
    leq-is-emb-count {f} H = leq-emb-count (pair f H)

  abstract
    leq-is-injective-count :
      {f : A → B} → is-injective f →
      (number-of-elements-count eA) ≤-ℕ (number-of-elements-count eB)
    leq-is-injective-count H =
      leq-is-emb-count (is-emb-is-injective (is-set-count eB) H)

  abstract
    is-not-emb-le-count :
      (f : A → B) →
      le-ℕ (number-of-elements-count eB) (number-of-elements-count eA) →
      ¬ (is-emb f)
    is-not-emb-le-count f p H =
      is-not-emb-le-Fin
        ( number-of-elements-count eA)
        ( number-of-elements-count eB)
        ( map-emb h)
        ( p)
        ( is-emb-map-emb h)
      where
      h : Fin (number-of-elements-count eA) ↪ Fin (number-of-elements-count eB)
      h = comp-emb
            ( emb-equiv (inv-equiv-count eB))
            ( comp-emb (pair f H) (emb-equiv (equiv-count eA)))

  abstract
    is-not-injective-le-count :
      (f : A → B) →
      le-ℕ (number-of-elements-count eB) (number-of-elements-count eA) →
      ¬ (is-injective f)
    is-not-injective-le-count f p H =
      is-not-emb-le-count f p (is-emb-is-injective (is-set-count eB) H)

abstract
  no-embedding-ℕ-count :
    {l : Level} {A : UU l} (e : count A) → ¬ (ℕ ↪ A)
  no-embedding-ℕ-count e f =
    no-embedding-ℕ-Fin
    ( number-of-elements-count e)
    ( comp-emb (emb-equiv (inv-equiv-count e)) f)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (eA : count A) (eB : count B)
  (f : A → B)
  (p : le-ℕ (number-of-elements-count eB) (number-of-elements-count eA))
  where

  repetition-le-count : repetition f
  repetition-le-count =
    map-equiv-repetition
      ( (map-inv-equiv-count eB ∘ f) ∘ (map-equiv-count eA))
      ( f)
      ( equiv-count eA)
      ( equiv-count eB)
      ( issec-map-inv-equiv-count eB ·r (f ∘ (map-equiv-count eA)))
      ( repetition-le-Fin
        ( number-of-elements-count eA)
        ( number-of-elements-count eB)
        ( (map-inv-equiv-count eB ∘ f) ∘ (map-equiv-count eA))
        ( p))

  pair-of-distinct-elements-repetition-le-count :
    pair-of-distinct-elements A
  pair-of-distinct-elements-repetition-le-count = pr1 repetition-le-count

  fst-repetition-le-count : A
  fst-repetition-le-count =
    fst-pair-of-distinct-elements
      pair-of-distinct-elements-repetition-le-count

  snd-repetition-le-count : A
  snd-repetition-le-count =
    snd-pair-of-distinct-elements
      pair-of-distinct-elements-repetition-le-count

  distinction-repetition-le-count :
    ¬ (Id fst-repetition-le-count snd-repetition-le-count)
  distinction-repetition-le-count =
    distinction-pair-of-distinct-elements
      pair-of-distinct-elements-repetition-le-count

  is-repetition-pair-of-distinct-elements-repetition-le-count :
    is-repetition-pair-of-distinct-elements f
      pair-of-distinct-elements-repetition-le-count
  is-repetition-pair-of-distinct-elements-repetition-le-count =
    is-repetition-pair-of-distinct-elements-repetition f
      repetition-le-count
```

### The pigeonhole principle for finite types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (H : is-finite A) (K : is-finite B)
  where

  abstract
    leq-emb-is-finite :
      (A ↪ B) →
      (number-of-elements-is-finite H) ≤-ℕ (number-of-elements-is-finite K)
    leq-emb-is-finite f =
      apply-universal-property-trunc-Prop H P
        ( λ eA →
          apply-universal-property-trunc-Prop K P
            ( λ eB →
              concatenate-eq-leq-eq-ℕ
                ( inv (compute-number-of-elements-is-finite eA H))
                ( leq-emb-count eA eB f)
                ( compute-number-of-elements-is-finite eB K)))
      where
      P : Prop lzero
      P = leq-ℕ-Prop
            ( number-of-elements-is-finite H)
            ( number-of-elements-is-finite K)

  abstract
    leq-is-emb-is-finite :
      {f : A → B} → is-emb f →
      (number-of-elements-is-finite H) ≤-ℕ (number-of-elements-is-finite K)
    leq-is-emb-is-finite {f} H =
      leq-emb-is-finite (pair f H)

  abstract
    leq-is-injective-is-finite :
      {f : A → B} → is-injective f →
      (number-of-elements-is-finite H) ≤-ℕ (number-of-elements-is-finite K)
    leq-is-injective-is-finite I =
      leq-is-emb-is-finite (is-emb-is-injective (is-set-is-finite K) I)

  abstract
    is-not-emb-le-is-finite :
      (f : A → B) →
      le-ℕ (number-of-elements-is-finite K) (number-of-elements-is-finite H) →
      ¬ (is-emb f)
    is-not-emb-le-is-finite f p E =
      apply-universal-property-trunc-Prop H empty-Prop
        ( λ e →
          apply-universal-property-trunc-Prop K empty-Prop
            ( λ d → is-not-emb-le-count e d f
              ( concatenate-eq-le-eq-ℕ
                ( compute-number-of-elements-is-finite d K)
                ( p)
                ( inv (compute-number-of-elements-is-finite e H)))
              ( E)))

  abstract
    is-not-injective-le-is-finite :
      (f : A → B) →
      le-ℕ (number-of-elements-is-finite K) (number-of-elements-is-finite H) →
      ¬ (is-injective f)
    is-not-injective-le-is-finite f p I =
      is-not-emb-le-is-finite f p (is-emb-is-injective (is-set-is-finite K) I)

abstract
  no-embedding-ℕ-is-finite :
    {l : Level} {A : UU l} (H : is-finite A) → ¬ (ℕ ↪ A)
  no-embedding-ℕ-is-finite H f =
    apply-universal-property-trunc-Prop H empty-Prop
      ( λ e → no-embedding-ℕ-count e f)
```

###

```agda
-- We define the predicate that the value of f at x is a value of f at another y

is-repetition :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (a : A) → UU (l1 ⊔ l2)
is-repetition {l1} {l2} {A} {B} f a = Σ A (λ x → ¬ (Id a x) × (Id (f a) (f x)))

-- On the standard finite sets, is-repetition f a is decidable

is-decidable-is-repetition-Fin :
  {k l : ℕ} (f : Fin k → Fin l) (x : Fin k) → is-decidable (is-repetition f x)
is-decidable-is-repetition-Fin f x =
  is-decidable-Σ-Fin
    ( λ y →
      is-decidable-prod
        ( is-decidable-neg (has-decidable-equality-Fin x y))
        ( has-decidable-equality-Fin (f x) (f y)))

-- We define the predicate that f maps two different elements to the same value

has-repetition :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → UU (l1 ⊔ l2)
has-repetition {A = A} f = Σ A (is-repetition f)

has-repetition-comp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (g : B → C)
  {f : A → B} → has-repetition f → has-repetition (g ∘ f)
has-repetition-comp g (pair x (pair y (pair s t))) =
  pair x (pair y (pair s (ap g t)))

has-repetition-left-factor :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {g : B → C}
  {f : A → B} → is-emb f → has-repetition (g ∘ f) → has-repetition g
has-repetition-left-factor {g = g} {f} H (pair a (pair b (pair K p))) =
  pair (f a) (pair (f b) (pair (λ q → K (is-injective-is-emb H q)) p))

has-repetition-right-factor :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {g : B → C}
  {f : A → B} → is-emb g → has-repetition (g ∘ f) → has-repetition f
has-repetition-right-factor {g = g} {f} H (pair a (pair b (pair K p))) =
  pair a (pair b (pair K (is-injective-is-emb H p)))

-- On the standard finite sets, has-repetition f is decidable

is-decidable-has-repetition-Fin :
  {k l : ℕ} (f : Fin k → Fin l) → is-decidable (has-repetition f)
is-decidable-has-repetition-Fin f =
  is-decidable-Σ-Fin (is-decidable-is-repetition-Fin f)

-- If f is not injective, then it has a repetition.

is-injective-map-Fin-zero-Fin :
  {k : ℕ} (f : Fin zero-ℕ → Fin k) → is-injective f
is-injective-map-Fin-zero-Fin f {()} {y}

is-injective-map-Fin-one-Fin :
  {k : ℕ} (f : Fin one-ℕ → Fin k) → is-injective f
is-injective-map-Fin-one-Fin f {inr star} {inr star} p = refl

has-repetition-is-not-injective-Fin :
  {k l : ℕ} (f : Fin l → Fin k) → is-not-injective f → has-repetition f
has-repetition-is-not-injective-Fin {l = zero-ℕ} f H =
  ex-falso (H (is-injective-map-Fin-zero-Fin f))
has-repetition-is-not-injective-Fin {l = succ-ℕ l} f H with
  is-decidable-is-repetition-Fin f (inr star)
... | inl r = pair (inr star) r
... | inr g = α (has-repetition-is-not-injective-Fin {l = l} (f ∘ inl) K)
  where
  K : is-not-injective (f ∘ inl)
  K I = H (λ {x} {y} → J x y)
    where
    J : (x y : Fin (succ-ℕ l)) → Id (f x) (f y) → Id x y
    J (inl x) (inl y) p = ap inl (I p)
    J (inl x) (inr star) p = ex-falso (g (triple (inl x) Eq-Fin-eq (inv p)))
    J (inr star) (inl y) p = ex-falso (g (triple (inl y) Eq-Fin-eq p))
    J (inr star) (inr star) p = refl
  α : has-repetition (f ∘ inl) → has-repetition f
  α (pair x (pair y (pair h q))) =
    pair (inl x) (pair (inl y) (pair (λ r → h (is-injective-inl r)) q))
```

```agda
has-repetition-le-Fin :
  {k l : ℕ} (f : Fin k → Fin l) → le-ℕ l k → has-repetition f
has-repetition-le-Fin f p =
  has-repetition-is-not-injective-Fin f (is-not-injective-le-Fin f p)

has-repetition-le-count :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (eA : count A) (eB : count B) →
  (f : A → B) →
  le-ℕ (number-of-elements-count eB) (number-of-elements-count eA) →
  has-repetition f
has-repetition-le-count eA eB f p =
  has-repetition-right-factor
    ( is-emb-is-equiv (is-equiv-map-inv-equiv (equiv-count eB)))
    ( has-repetition-left-factor
      ( is-emb-is-equiv (is-equiv-map-equiv (equiv-count eA)))
      ( has-repetition-le-Fin
        ( map-equiv (inv-equiv-count eB) ∘ (f ∘ map-equiv-count eA))
        ( p)))

has-repetition-Fin-succ-to-Fin :
  {k : ℕ} (f : Fin (succ-ℕ k) → Fin k) → has-repetition f
has-repetition-Fin-succ-to-Fin {k} f =
  has-repetition-le-Fin f (le-succ-ℕ {k})

has-repetition-nat-to-Fin :
  {k : ℕ} (f : ℕ → Fin k) → has-repetition f
has-repetition-nat-to-Fin {k} f =
  has-repetition-left-factor
    ( is-emb-nat-Fin {succ-ℕ k})
    ( has-repetition-Fin-succ-to-Fin (f ∘ nat-Fin))

has-repetition-nat-to-count :
  {l : Level} {A : UU l} (e : count A) (f : ℕ → A) → has-repetition f
has-repetition-nat-to-count e f =
  has-repetition-right-factor
    ( is-emb-is-equiv (is-equiv-map-inv-equiv (equiv-count e)))
    ( has-repetition-nat-to-Fin (map-inv-equiv-count e ∘ f))
```

### Ordered repetitions of maps out of the natural numbers

```agda
is-ordered-repetition-ℕ :
  {l1 : Level} {A : UU l1} (f : ℕ → A) (x : ℕ) → UU l1
is-ordered-repetition-ℕ f x = Σ ℕ (λ y → (le-ℕ y x) × Id (f y) (f x))

is-decidable-is-ordered-repetition-ℕ-Fin :
  {k : ℕ} (f : ℕ → Fin k) (x : ℕ) → is-decidable (is-ordered-repetition-ℕ f x)
is-decidable-is-ordered-repetition-ℕ-Fin f x =
  is-decidable-strictly-bounded-Σ-ℕ' x
    ( λ y → Id (f y) (f x))
    ( λ y → has-decidable-equality-Fin (f y) (f x))

is-decidable-is-ordered-repetition-ℕ-count :
  {l : Level} {A : UU l} (e : count A) (f : ℕ → A) (x : ℕ) →
  is-decidable (is-ordered-repetition-ℕ f x)
is-decidable-is-ordered-repetition-ℕ-count e f x =
  is-decidable-strictly-bounded-Σ-ℕ' x
    ( λ y → Id (f y) (f x))
    ( λ y → has-decidable-equality-count e (f y) (f x))

has-ordered-repetition-ℕ :
  {l1 : Level} {A : UU l1} (f : ℕ → A) → UU l1
has-ordered-repetition-ℕ f = Σ ℕ (is-ordered-repetition-ℕ f)

has-ordered-repetition-comp-ℕ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (g : A → B) {f : ℕ → A} →
  has-ordered-repetition-ℕ f → has-ordered-repetition-ℕ (g ∘ f)
has-ordered-repetition-comp-ℕ g (pair a (pair b (pair H p))) =
  pair a (pair b (pair H (ap g p)))

has-ordered-repetition-right-factor-ℕ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {g : A → B} {f : ℕ → A} →
  is-emb g → has-ordered-repetition-ℕ (g ∘ f) → has-ordered-repetition-ℕ f
has-ordered-repetition-right-factor-ℕ E (pair a (pair b (pair H p))) =
  pair a (pair b (pair H (is-injective-is-emb E p)))

has-ordered-repetition-nat-to-Fin :
  {k : ℕ} (f : ℕ → Fin k) → has-ordered-repetition-ℕ f
has-ordered-repetition-nat-to-Fin f with
  has-repetition-nat-to-Fin f
... | pair x (pair y (pair H p)) with is-decidable-le-ℕ y x
... | inl t = pair x (pair y (pair t (inv p)))
... | inr t = pair y (pair x (pair L p))
  where
  L : le-ℕ x y
  L = map-left-unit-law-coprod-is-empty
        ( Id y x)
        ( le-ℕ x y)
        ( λ q → H (inv q))
        ( map-left-unit-law-coprod-is-empty
          ( le-ℕ y x)
          ( coprod (Id y x)
          ( le-ℕ x y))
          ( t)
          ( linear-le-ℕ y x))

has-ordered-repetition-nat-to-count :
  {l : Level} {A : UU l} (e : count A) (f : ℕ → A) → has-ordered-repetition-ℕ f
has-ordered-repetition-nat-to-count e f =
  has-ordered-repetition-right-factor-ℕ
    ( is-emb-is-equiv (is-equiv-map-inv-equiv (equiv-count e)))
    ( has-ordered-repetition-nat-to-Fin
      ( map-inv-equiv-count e ∘ f))

first-repetition-nat-to-Fin :
  {k : ℕ} (f : ℕ → Fin k) →
  minimal-element-ℕ (λ x → Σ ℕ (λ y → (le-ℕ y x) × (Id (f y) (f x))))
first-repetition-nat-to-Fin f =
  well-ordering-principle-ℕ
    ( λ x → Σ ℕ (λ y → (le-ℕ y x) × (Id (f y) (f x))))
    ( λ x → is-decidable-strictly-bounded-Σ-ℕ' x
              ( λ y → Id (f y) (f x))
              ( λ y → has-decidable-equality-Fin (f y) (f x)))
    ( has-ordered-repetition-nat-to-Fin f)
```
