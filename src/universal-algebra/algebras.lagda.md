# Cumulative hierarchy

```agda
module universal-algebra.algebras where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.groups

open import linear-algebra.vectors
```

</details>

## Idea

Universal algebra studies many different algebraic structures at the same time.
Given a signature, that is a collection of function symbols with a given arity,
an algebra consists of a carrier set together with an operation `f` of arity `n`
for each function symbol `f'` of arity `n`. The carrier and operations may also
require additional rules involving them.

## Definitions

### Signatures

```agda
signature : (l : Level) → UU (lsuc l)
signature (l) = Σ (UU l) (λ operations → (operations → ℕ))

operations-signature : {l : Level} → signature l → UU l
operations-signature Sig = pr1 Sig

arity-operations-signature :
  { l : Level} →
  ( Sig : signature l) →
  ( operations-signature Sig → ℕ)
arity-operations-signature Sig = pr2 Sig
```

### Models

A model of a signature `Sig` in a type `A` is a dependent function that assings
to each function symbol `f` of arity `n` and a vector of `n` elements of `A` an
element of `A`.

```agda
module _ {l1 : Level} (Sig : signature l1) where

  is-model : {l2 : Level} → UU l2 → UU (l1 ⊔ l2)
  is-model X =
    ( f : operations-signature Sig) →
    ( vec X (arity-operations-signature Sig f) → X)

  is-model-Set : {l2 : Level} → (Set l2) → UU (l1 ⊔ l2)
  is-model-Set X = is-model (type-Set X)

  Model : (l2 : Level) → UU (l1 ⊔ lsuc l2)
  Model l2 = Σ (Set l2) (λ X → is-model-Set X)

  set-Model : {l2 : Level} → Model l2 → Set l2
  set-Model M = pr1 M

  is-model-set-Model :
    { l2 : Level} →
    ( M : Model l2) →
    is-model-Set (set-Model M)
  is-model-set-Model M = pr2 M

  type-Model : {l2 : Level} → Model l2 → UU l2
  type-Model M = pr1 (set-Model M)

  is-set-type-Model :
    { l2 : Level} →
    ( M : Model l2) →
    is-set (type-Model M)
  is-set-type-Model M = pr2 (set-Model M)
```

### Terms

A term in a signature, is an abstract representation of a well formed expression
which uses only variables and operations in the signature. For this particular
formalization, we are using de Bruijn variables.

```agda
  data Term : UU l1 where
    var-Term : ℕ → Term
    op-Term : is-model Term
```

### Assignment of variables

An assignment of variables, assigns each de Bruijn variable to an element in a
type.

```agda
  assignment : {l2 : Level} → (A : UU l2) → UU l2
  assignment A = ℕ → A
```

### Evaluation of terms

Given a model of a type `A` and an assignment of variables, any term can be
evaluated to a concrete element of the type `A`.

```agda
  eval-term :
    {l2 : Level} → {A : UU l2} →
    is-model A → assignment A → Term → A

  eval-vec :
    { l2 : Level} → {A : UU l2} {n : ℕ} →
    is-model A → assignment A → vec Term n → vec A n

  eval-term m assign (var-Term n) = assign n
  eval-term m assign (op-Term f x) = m f (eval-vec m assign x)

  eval-vec m assign empty-vec = empty-vec
  eval-vec m assign (x ∷ v) = eval-term m assign x ∷ eval-vec m assign v
```

### Abstract equations

An abstract equation is a pair of terms.

```agda
  Abstract-Equation : UU l1
  Abstract-Equation = Term × Term

  lhs-Abstract-Equation : Abstract-Equation → Term
  lhs-Abstract-Equation = pr1

  rhs-Abstract-Equation : Abstract-Equation → Term
  rhs-Abstract-Equation = pr2
```

### Theories

A theory is a family of equations that should hold.

```agda
  Theory : {l2 : Level} → UU (l1 ⊔ lsuc l2)
  Theory {l2} = Σ (UU l2) (λ B → (B → Abstract-Equation))

  index-Theory : {l2 : Level} → Theory → UU l2
  index-Theory = pr1

  index-Abstract-Equation-Theory :
    { l2 : Level}
    ( Th : Theory {l2}) →
    ( index-Theory Th) →
    Abstract-Equation
  index-Abstract-Equation-Theory Th e = pr2 Th e
```

### Algebra

Given a theory, an algebra is a model on a set such that it satisfies all
equations.

```agda
  is-algebra :
    { l2 l3 : Level} →
    Theory {l2} → ( X : Model l3) → UU (l2 ⊔ l3)
  is-algebra Th M =
    ( e : index-Theory Th) →
    ( assign : assignment (type-Model M)) →
    eval-term (is-model-set-Model M) assign
      ( lhs-Abstract-Equation (index-Abstract-Equation-Theory Th e)) ＝
      eval-term (is-model-set-Model M) assign
        ( rhs-Abstract-Equation (index-Abstract-Equation-Theory Th e))

  Algebra :
    { l2 : Level} ( l3 : Level) →
    Theory {l2} → UU (l1 ⊔ l2 ⊔ lsuc l3)
  Algebra l3 Th =
    Σ ( Model l3) (is-algebra Th)

  model-Algebra :
    { l2 l3 : Level} →
    { Th : Theory {l2}} →
    Algebra l3 Th → Model l3
  model-Algebra Alg = pr1 Alg

  set-Algebra :
    { l2 l3 : Level} →
    { Th : Theory {l2}} →
    Algebra l3 Th → Set l3
  set-Algebra Alg = pr1 (pr1 Alg)

  is-model-set-Algebra :
    { l2 l3 : Level} →
    { Th : Theory {l2}} →
    ( Alg : Algebra l3 Th) →
    is-model-Set (set-Algebra {l2} {l3} {Th} Alg)
  is-model-set-Algebra Alg = pr2 (pr1 Alg)

  type-Algebra :
    { l2 l3 : Level} →
    { Th : Theory {l2}} →
    Algebra l3 Th → UU l3
  type-Algebra Alg =
    pr1 (pr1 (pr1 Alg))

  is-algebra-Algebra :
    { l2 l3 : Level} →
    { Th : Theory {l2}} →
    ( Alg : Algebra l3 Th) →
    is-algebra Th (model-Algebra {l2} {l3} {Th} Alg)
  is-algebra-Algebra Alg = pr2 Alg
```

## Properties

### Being an algebra is a proposition

```agda
  is-prop-is-algebra :
    { l2 l3 : Level} →
    { Th : Theory {l2}} →
    ( X : Model l3) →
    is-prop (is-algebra Th X)
  is-prop-is-algebra M =
    is-prop-Π
      ( λ e →
        ( is-prop-Π
          ( λ assign → is-set-type-Model M _ _)))
```

## Examples

### The algebra of groups

```agda
data group-ops : UU lzero where
  unit-group-op mul-group-op inv-group-op : group-ops

group-signature : signature lzero
group-signature =
  pair
    group-ops
    ( λ { unit-group-op → 0;
          mul-group-op → 2;
          inv-group-op → 1})

data group-laws : UU lzero where
  assoc-l-group-laws : group-laws
  invl-l-group-laws : group-laws
  invr-r-group-laws : group-laws
  idl-l-group-laws : group-laws
  idr-r-group-laws : group-laws

group-Theory : Theory group-signature
group-Theory =
  pair
    group-laws
    ( λ { assoc-l-group-laws →
            pair
              ( op mul-group-op
                ( ( op mul-group-op
                  ( var 0 ∷ var 1 ∷ empty-vec)) ∷
                ( var 2) ∷ empty-vec))
              ( op mul-group-op
                ( var 0 ∷
                ( op mul-group-op (var 1 ∷ var 2 ∷ empty-vec)) ∷ empty-vec));
          invl-l-group-laws →
            pair
              ( op mul-group-op
                ( op inv-group-op (var 0 ∷ empty-vec) ∷ var 0 ∷ empty-vec))
              (op unit-group-op empty-vec);
          invr-r-group-laws →
            pair
              ( op mul-group-op
                ( var 0 ∷ op inv-group-op (var 0 ∷ empty-vec) ∷ empty-vec))
              (op unit-group-op empty-vec);
          idl-l-group-laws →
            pair
              (op mul-group-op (op unit-group-op empty-vec ∷ var 0 ∷ empty-vec))
              (var 0);
          idr-r-group-laws →
            pair
              (op mul-group-op (var 0 ∷ op unit-group-op empty-vec ∷ empty-vec))
              (var 0)})
  where
    op = op-Term
    var = var-Term

group-Algebra-Group :
  {l2 : Level} →
  Algebra group-signature l2 group-Theory →
  Group l2
group-Algebra-Group (((A , is-set-A) , models-A) , satisfies-A) =
  pair
    ( pair
      ( pair A is-set-A)
      ( pair
        ( λ x y →
          ( models-A mul-group-op (x ∷ y ∷ empty-vec)))
        ( λ x y z →
          ( satisfies-A assoc-l-group-laws
            ( λ { zero-ℕ → x;
                ( succ-ℕ zero-ℕ) → y;
                ( succ-ℕ (succ-ℕ n)) → z})))))
    ( pair
      ( pair
        ( models-A unit-group-op empty-vec)
        ( pair
          ( λ x → satisfies-A idl-l-group-laws (λ _ → x))
          ( λ x → satisfies-A idr-r-group-laws (λ _ → x))))
      ( pair
        ( λ x → models-A inv-group-op (x ∷ empty-vec))
        ( pair
          ( λ x → satisfies-A invl-l-group-laws (λ _ → x))
          ( λ x → satisfies-A invr-r-group-laws (λ _ → x)))))

Group-group-Algebra :
  {l2 : Level} →
  Group l2 →
  Algebra group-signature l2 group-Theory
Group-group-Algebra G =
  pair
    ( pair
      ( ( set-Group G))
      ( λ { unit-group-op v → unit-Group G;
            mul-group-op (x ∷ y ∷ empty-vec) → mul-Group G x y;
            inv-group-op (x ∷ empty-vec) → inv-Group G x}))
    ( λ { assoc-l-group-laws assign →
            associative-mul-Group G (assign 0) (assign 1) (assign 2);
          invl-l-group-laws assign →
            left-inverse-law-mul-Group G (assign 0);
          invr-r-group-laws assign →
            right-inverse-law-mul-Group G (assign 0);
          idl-l-group-laws assign →
            left-unit-law-mul-Group G (assign 0);
          idr-r-group-laws assign →
            right-unit-law-mul-Group G (assign 0)})

equiv-group-Algebra-Group :
  {l2 : Level} →
  Algebra group-signature l2 group-Theory ≃
  Group l2
equiv-group-Algebra-Group {l2} =
  pair
    ( group-Algebra-Group)
    ( pair
      ( pair
         ( Group-group-Algebra)
         ( λ G →
           ( eq-pair-Σ refl
             ( eq-is-prop
               ( is-prop-is-group (semigroup-Group G))))))
      ( pair
        ( Group-group-Algebra)
        ( λ Alg →
          ( eq-pair-Σ
            ( eq-pair-Σ
              ( refl)
              ( eq-htpy
                ( λ { unit-group-op →
                      ( eq-htpy λ {empty-vec → refl});
                      mul-group-op →
                      ( eq-htpy λ { (x ∷ y ∷ empty-vec) → refl});
                      inv-group-op →
                      ( eq-htpy λ { (x ∷ empty-vec) → refl})}))))
          ( eq-is-prop
            ( is-prop-is-algebra
              ( group-signature) {lzero} {l2} {group-Theory}
              ( model-Algebra group-signature {lzero} {l2} {group-Theory} Alg))))))
```
