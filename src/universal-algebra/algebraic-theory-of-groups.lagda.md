# Algebraic theory of groups

```agda
module universal-algebra.algebraic-theory-of-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.groups

open import linear-algebra.vectors

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-theories
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

There is an algebraic theory of groups. They type of all such algebras is
equivalent to the type of groups.

## Definitions

### The algebra of groups

```agda
data group-ops : UU lzero where
  unit-group-op mul-group-op inv-group-op : group-ops

group-signature : signature lzero
pr1 group-signature = group-ops
pr2 group-signature unit-group-op = 0
pr2 group-signature mul-group-op = 2
pr2 group-signature inv-group-op = 1

data group-laws : UU lzero where
  associative-l-group-laws : group-laws
  invl-l-group-laws : group-laws
  invr-r-group-laws : group-laws
  idl-l-group-laws : group-laws
  idr-r-group-laws : group-laws

group-Theory : Theory group-signature lzero
pr1 group-Theory = group-laws
pr2 group-Theory =
  λ where
  associative-l-group-laws →
    ( op mul-group-op
      ( ( op mul-group-op (var 0 ∷ var 1 ∷ empty-vec)) ∷ var 2 ∷ empty-vec)) ,
    ( op mul-group-op
      ( var 0 ∷ (op mul-group-op (var 1 ∷ var 2 ∷ empty-vec)) ∷ empty-vec))
  invl-l-group-laws →
    ( op mul-group-op
      ( op inv-group-op (var 0 ∷ empty-vec) ∷ var 0 ∷ empty-vec)) ,
    ( op unit-group-op empty-vec)
  invr-r-group-laws →
    ( op mul-group-op
      ( var 0 ∷ op inv-group-op (var 0 ∷ empty-vec) ∷ empty-vec)) ,
    ( op unit-group-op empty-vec)
  idl-l-group-laws →
    ( op mul-group-op (op unit-group-op empty-vec ∷ var 0 ∷ empty-vec)) ,
    ( var 0)
  idr-r-group-laws →
    ( op mul-group-op (var 0 ∷ op unit-group-op empty-vec ∷ empty-vec)) ,
    ( var 0)
    where
    op = op-Term
    var = var-Term

group-Algebra : (l : Level) → UU (lsuc l)
group-Algebra l = Algebra group-signature group-Theory l
```

## Properties

### The algebra of groups is equivalent to the type of groups

```agda
group-Algebra-Group :
  {l : Level} →
  Algebra group-signature group-Theory l →
  Group l
pr1 (pr1 (group-Algebra-Group ((A-Set , models-A) , satisfies-A))) = A-Set
pr1 (pr2 (pr1 (group-Algebra-Group ((A-Set , models-A) , satisfies-A)))) x y =
  models-A mul-group-op (x ∷ y ∷ empty-vec)
pr2 (pr2 (pr1 (group-Algebra-Group ((A-Set , models-A) , satisfies-A)))) x y z =
  satisfies-A associative-l-group-laws
    ( λ { 0 → x ; 1 → y ; (succ-ℕ (succ-ℕ n)) → z})
pr1 (pr1 (pr2 (group-Algebra-Group ((A-Set , models-A) , satisfies-A)))) =
  models-A unit-group-op empty-vec
pr1 (pr2 (pr1 (pr2 (group-Algebra-Group (_ , satisfies-A))))) x =
  satisfies-A idl-l-group-laws (λ _ → x)
pr2 (pr2 (pr1 (pr2 (group-Algebra-Group (_ , satisfies-A))))) x =
  satisfies-A idr-r-group-laws (λ _ → x)
pr1 (pr2 (pr2 (group-Algebra-Group ((A-Set , models-A) , satisfies-A)))) x =
  models-A inv-group-op (x ∷ empty-vec)
pr1 (pr2 (pr2 (pr2 (group-Algebra-Group (_ , satisfies-A))))) x =
  satisfies-A invl-l-group-laws (λ _ → x)
pr2 (pr2 (pr2 (pr2 (group-Algebra-Group (_ , satisfies-A))))) x =
  satisfies-A invr-r-group-laws (λ _ → x)

Group-group-Algebra :
  {l : Level} →
  Group l →
  Algebra group-signature group-Theory l
Group-group-Algebra G =
  pair
    ( pair
      ( ( set-Group G))
      ( λ where
        unit-group-op v → unit-Group G
        mul-group-op (x ∷ y ∷ empty-vec) → mul-Group G x y
        inv-group-op (x ∷ empty-vec) → inv-Group G x))
    ( λ where
      associative-l-group-laws assign →
        associative-mul-Group G (assign 0) (assign 1) (assign 2)
      invl-l-group-laws assign →
        left-inverse-law-mul-Group G (assign 0)
      invr-r-group-laws assign →
        right-inverse-law-mul-Group G (assign 0)
      idl-l-group-laws assign →
        left-unit-law-mul-Group G (assign 0)
      idr-r-group-laws assign →
        right-unit-law-mul-Group G (assign 0))

abstract
  equiv-group-Algebra-Group :
    {l : Level} →
    Algebra group-signature group-Theory l ≃
    Group l
  pr1 equiv-group-Algebra-Group = group-Algebra-Group
  pr1 (pr1 (pr2 equiv-group-Algebra-Group)) = Group-group-Algebra
  pr2 (pr1 (pr2 equiv-group-Algebra-Group)) G =
    eq-pair-eq-fiber
      ( eq-is-prop (is-prop-is-group-Semigroup (semigroup-Group G)))
  pr1 (pr2 (pr2 equiv-group-Algebra-Group)) = Group-group-Algebra
  pr2 (pr2 (pr2 equiv-group-Algebra-Group)) A =
    eq-pair-Σ
      ( eq-pair-eq-fiber
        ( eq-htpy
          ( λ where
            unit-group-op → eq-htpy (λ where empty-vec → refl)
            mul-group-op → eq-htpy (λ where (x ∷ y ∷ empty-vec) → refl)
            inv-group-op → eq-htpy (λ where (x ∷ empty-vec) → refl))))
      ( eq-is-prop
        ( is-prop-is-algebra
          ( group-signature) ( group-Theory)
          ( model-Algebra group-signature group-Theory A)))
```
