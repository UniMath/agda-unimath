---
title: Group solver
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.group-solver where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equational-reasoning using (step-equational-reasoning ; _∎)
open import foundation.identity-types using (Id; _＝_; ap-binary; inv; _∙_; ap; refl)
open import foundation.sets using (UU-Set; is-set; Id-Prop)
open import foundation.universe-levels using (Level; UU; lsuc)

open import group-theory.groups using
  ( Group; type-Group; mul-Group; set-Group; is-set-type-Group
  ; inv-Group ; unit-Group ; associative-mul-Group
  ; right-inverse-law-mul-Group ; left-inverse-law-mul-Group
  ; right-unit-law-mul-Group ; left-unit-law-mul-Group
  ; distributive-inv-mul-Group ; inv-inv-Group
  )

```


## Idea

This module simplifies group expressions, such that all items associate the same way
and removes units and inverses next to the original

```agda

module _
  {l : Level} (G : Group l)
  where

```

## Properties


```agda

  private
    -- Shorter names to make the proofs less verbose
    _*_ = mul-Group G
    infixl 30 _*_
    _⁻¹ = inv-Group G
    infix 40 _⁻¹
    unit = unit-Group G

  open import elementary-number-theory.natural-numbers using
    ( ℕ; zero-ℕ; succ-ℕ; is-zero-ℕ; is-one-ℕ; is-not-one-ℕ; is-set-ℕ)

  open import linear-algebra.vectors
  -- open import univalent-combinatorics.standard-finite-types
  open import univalent-combinatorics.lists
  open import foundation.decidable-types
  open import foundation.coproduct-types using
    ( _+_; inl; inr; ind-coprod; is-prop-coprod; is-left; is-right)
  open import group-theory.groups using (inv-unit-Group)

  data Fin : ℕ → UU where
    zero-Fin : ∀ {n} → Fin (succ-ℕ n)
    succ-Fin : ∀ {n} → Fin n → Fin (succ-ℕ n)

  finEq : ∀ {n} → (a b : Fin n) → is-decidable (Id a b)
  finEq zero-Fin zero-Fin = inl refl
  finEq zero-Fin (succ-Fin b) = inr (λ ())
  finEq (succ-Fin a) zero-Fin = inr (λ ())
  finEq (succ-Fin a) (succ-Fin b) with finEq a b
  ... | inl eq = inl (ap succ-Fin eq)
  ... | inr neq = inr (λ { refl → neq refl})

  getVec : ∀ {n} {l} {A : UU l} → vec A n → Fin n → A
  getVec (x ∷ v) zero-Fin = x
  getVec (x ∷ v) (succ-Fin k) = getVec v k

  data GroupSyntax (n : ℕ) : UU where
    gUnit : GroupSyntax n
    gMul : GroupSyntax n → GroupSyntax n → GroupSyntax n
    gInv : GroupSyntax n → GroupSyntax n
    inner : Fin n → GroupSyntax n

  Env : ℕ → UU l → UU l
  Env n A = vec A n

  unQuoteGS : ∀ {n} → GroupSyntax n → Env n (type-Group G) → type-Group G
  unQuoteGS gUnit e = unit-Group G
  unQuoteGS (gMul x y) e = mul-Group G (unQuoteGS x e) (unQuoteGS y e)
  unQuoteGS (gInv x) e = inv-Group G (unQuoteGS x e)
  unQuoteGS (inner x) e = getVec e x

  data SimpleElem  (n : ℕ) : UU where
    inv-SE : Fin n → SimpleElem n
    pure-SE : Fin n → SimpleElem n

  inv-SE' : ∀ {n} → SimpleElem n → SimpleElem n
  inv-SE' (inv-SE k) = pure-SE k
  inv-SE' (pure-SE k) = inv-SE k

  Simple : (n : ℕ) → UU
  Simple n = list (SimpleElem n)

  module _ {n : ℕ} where
    unquoteSimpleElem : SimpleElem n → GroupSyntax n
    unquoteSimpleElem (inv-SE x) = gInv (inner x)
    unquoteSimpleElem (pure-SE x) = inner x

    unquoteSimple : Simple n → GroupSyntax n
    unquoteSimple nil = gUnit
    unquoteSimple (cons x xs) = gMul (unquoteSimpleElem x) (unquoteSimple xs)
    -- unquoteSimple (cons x nil) = unquoteSimpleElem x
    -- unquoteSimple (cons x xs@(cons _ _)) = gMul (unquoteSimpleElem x) (unquoteSimple xs)

    concat-simplify : Simple n → Simple n → Simple n
    concat-simplify nil b = b
    concat-simplify (cons x a) b with concat-simplify a b
    ... | nil = cons x nil
    concat-simplify (cons xi@(inv-SE x) _) _ | yab@(cons (inv-SE y) ab) = cons xi yab
    concat-simplify (cons xi@(inv-SE x) _) _ | yab@(cons (pure-SE y) ab) with finEq x y
    ... | inl eq = ab
    ... | inr neq = cons xi yab
    concat-simplify (cons xi@(pure-SE x) a) b | yab@(cons (inv-SE y) ab) with finEq x y
    ... | inl eq = ab
    ... | inr neq = cons xi yab
    concat-simplify (cons xi@(pure-SE x) a) b | yab@(cons (pure-SE y) ab) = cons xi yab

    simplifyGS : GroupSyntax n → Simple n
    simplifyGS gUnit = nil
    simplifyGS (gMul a b) = concat-simplify (simplifyGS a) (simplifyGS b)
    simplifyGS (gInv a) = reverse-list (map-list inv-SE' (simplifyGS a))
    -- simplifyGS (gInv a) = map-list inv-SE' (reverse-list (simplifyGS a))
    simplifyGS (inner n) = cons (pure-SE n) nil

    data GroupEquality : GroupSyntax n → GroupSyntax n → UU where
      refl-GE : ∀ {x} → GroupEquality x x
      sym-GE : ∀ {x} {y} → GroupEquality x y → GroupEquality y x
      _∙GE_ : ∀ {x} {y} {z} → GroupEquality x y → GroupEquality y z → GroupEquality x z

      ap-gMul : ∀ {x} {y} {z} {w} → GroupEquality x y → GroupEquality z w → GroupEquality (gMul x z) (gMul y w)
      ap-gInv : ∀ {x} {y} → GroupEquality x y → GroupEquality (gInv x) (gInv y)

      assoc-GE : ∀ x y z → GroupEquality (gMul (gMul x y) z) (gMul x (gMul y z))
      l-unit : ∀ x → GroupEquality (gMul gUnit x) x
      r-unit : ∀ x → GroupEquality (gMul x gUnit) x
      l-inv : ∀ x → GroupEquality (gMul (gInv x) x) gUnit
      r-inv : ∀ x → GroupEquality (gMul x (gInv x)) gUnit

      inv-unit-GE : GroupEquality (gInv gUnit) gUnit
      inv-inv-GE : ∀ x → GroupEquality (gInv (gInv x)) x
      distr-inv-mul-GE : ∀ x y → GroupEquality (gInv (gMul x y)) (gMul (gInv y) (gInv x))

    infixr 20 _∙GE_

    useGroupEquality
      : ∀ {x y : GroupSyntax n} (env : Env n (type-Group G))
      → GroupEquality x y → unQuoteGS x env ＝ unQuoteGS y env
    useGroupEquality env (refl-GE) = refl
    useGroupEquality env (sym-GE ge) = inv (useGroupEquality env ge)
    useGroupEquality env (_∙GE_ ge ge') = useGroupEquality env ge ∙ useGroupEquality env ge'
    -- useGroupEquality env (ap-gMul {y = y} refl-GE ge') = ap (unQuoteGS y env *_) (useGroupEquality env ge')
    useGroupEquality env (ap-gMul {y = y} {z = z} ge ge') =
      ap (_* (unQuoteGS z env)) (useGroupEquality env ge)
      ∙ ap (unQuoteGS y env *_) (useGroupEquality env ge')
    useGroupEquality env (ap-gInv ge) = ap (inv-Group G) (useGroupEquality env ge)
    useGroupEquality env (assoc-GE x y z) = associative-mul-Group G _ _ _
    useGroupEquality env (l-unit _) = left-unit-law-mul-Group G _
    useGroupEquality env (r-unit _) = right-unit-law-mul-Group G _
    useGroupEquality env (l-inv x) = left-inverse-law-mul-Group G _
    useGroupEquality env (r-inv x) = right-inverse-law-mul-Group G _
    useGroupEquality env inv-unit-GE = inv-unit-Group G
    useGroupEquality env (inv-inv-GE x) = inv-inv-Group G (unQuoteGS x env)
    useGroupEquality env (distr-inv-mul-GE x y) = distributive-inv-mul-Group G (unQuoteGS x env) (unQuoteGS y env)

    concat-simplify-valid : ∀ (u w : Simple n) →
                            GroupEquality (gMul (unquoteSimple u) (unquoteSimple w))
                            (unquoteSimple (concat-simplify u w))
    concat-simplify-valid nil b = l-unit (unquoteSimple b)
    concat-simplify-valid (cons x a) b with concat-simplify a b | concat-simplify-valid a b
    ... | nil | val = (assoc-GE _ _ _) ∙GE (ap-gMul refl-GE val)
    concat-simplify-valid (cons xi@(inv-SE x) _) _ | yab@(cons (inv-SE y) ab) | val =
      _∙GE_ (assoc-GE _ _ _) (ap-gMul refl-GE val)
    concat-simplify-valid (cons xi@(inv-SE x) _) _ | yab@(cons (pure-SE y) ab) | val with finEq x y
    ... | inl refl = _∙GE_ (assoc-GE _ _ _ ∙GE ap-gMul refl-GE val)
      (_∙GE_ (sym-GE (assoc-GE _ _ _)) (_∙GE_ (ap-gMul (l-inv _) refl-GE) (l-unit _)))
    ... | inr neq = _∙GE_ (assoc-GE _ _ _) (ap-gMul refl-GE val)
    concat-simplify-valid (cons xi@(pure-SE x) a) b | yab@(cons (inv-SE y) ab) | val with finEq x y
    ... | inl refl = _∙GE_ (_∙GE_ (assoc-GE _ _ _) (ap-gMul refl-GE val))
      (_∙GE_ (sym-GE (assoc-GE _ _ _)) (_∙GE_ (ap-gMul (r-inv _) refl-GE) (l-unit _)))
    ... | inr neq = _∙GE_ (assoc-GE _ _ _) (ap-gMul refl-GE val)
    concat-simplify-valid (cons xi@(pure-SE x) a) b | yab@(cons (pure-SE y) ab) | val =
      _∙GE_ (assoc-GE _ _ _) (ap-gMul refl-GE val)

    inv-single-valid : ∀ w → GroupEquality
      (gInv (unquoteSimpleElem w))
      (unquoteSimpleElem (inv-SE' w))
    inv-single-valid (inv-SE x) = inv-inv-GE (inner x)
    inv-single-valid (pure-SE x) = refl-GE


    -- inv-simplify-valid : ∀ (w : list (SimpleElem n)) →
    --                     GroupEquality (gInv (unquoteSimple w))
    --                     (unquoteSimple (map-list inv-SE' (reverse-list w)))
    -- inv-simplify-valid nil = inv-unit-GE
    -- inv-simplify-valid (cons x xs) = {!!}
    -- inv-simplify-valid (cons x xs) = _∙GE_
    --   (distr-inv-mul-GE (unquoteSimpleElem x) (unquoteSimple xs))
    --   (_∙GE_ (ap-gMul (inv-simplify-valid xs) (inv-single-valid x))
    --     {!gmul-concat!})

    -- inv-simplify-valid (cons x nil) = inv-single-valid x
    -- inv-simplify-valid (cons x ws@(cons y ys)) = {!IH!}
    --   where
    --     IH : GroupEquality (gInv (unquoteSimple ws))
    --            (unquoteSimple (map-list inv-SE' (reverse-list ws)))
    --     IH = inv-simplify-valid ws
    --     Goal : GroupEquality
    --       (gInv (gMul (unquoteSimpleElem x) (unquoteSimple (cons y ys))))
    --       (unquoteSimple
    --       (map-list inv-SE'
    --         (concat-list (concat-list (reverse-list ys) (in-list y))
    --         (in-list x))))
    --     Goal = {!!}

    gMul-concat' : ∀ (xs : Simple n)
                    (ys : Simple n) →
                  GroupEquality (gMul (unquoteSimple xs) (unquoteSimple ys))
                  (unquoteSimple
                  (concat-list xs ys))
    gMul-concat' nil bs = l-unit _
    gMul-concat' (cons x as) b = _∙GE_ (assoc-GE _ _ _) (ap-gMul refl-GE (gMul-concat' as b))

    gMul-concat-1 : ∀ (xs : Simple n)
                    (x : SimpleElem n) →
                  GroupEquality (gMul (unquoteSimple xs) (unquoteSimpleElem x))
                  (unquoteSimple
                  (concat-list xs (cons x nil)))
    gMul-concat-1 xs a = ap-gMul refl-GE (sym-GE (r-unit _)) ∙GE gMul-concat' xs (cons a nil)
    -- gMul-concat nil a = _∙GE_ (l-unit _) (sym-GE (r-unit _))
    -- gMul-concat (cons x as) a = {!!}

    inv-simplify-valid' : ∀ (w : list (SimpleElem n)) →
                        GroupEquality (gInv (unquoteSimple w))
                        (unquoteSimple (reverse-list (map-list inv-SE' w)))
    inv-simplify-valid' nil = inv-unit-GE
    inv-simplify-valid' (cons x xs) = _∙GE_
      (distr-inv-mul-GE (unquoteSimpleElem x) (unquoteSimple xs))
      (_∙GE_ (ap-gMul (inv-simplify-valid' xs) (inv-single-valid x))
      (gMul-concat-1 (reverse-list (map-list inv-SE' xs)) (inv-SE' x)))

    simplifyValid : ∀ (g : GroupSyntax n) → GroupEquality g (unquoteSimple (simplifyGS g))
    simplifyValid gUnit = refl-GE
    simplifyValid (gMul a b) =
      (ap-gMul (simplifyValid a) (simplifyValid b)) ∙GE
      (concat-simplify-valid (simplifyGS a) (simplifyGS b))
    simplifyValid (gInv g) = ap-gInv (simplifyValid g) ∙GE inv-simplify-valid' (simplifyGS g)
    simplifyValid (inner _) = sym-GE (r-unit _)
    -- simplifyValid (inner _) = refl-GE

  private
    _*'_ : ∀ {n} → GroupSyntax n → GroupSyntax n → GroupSyntax n
    _*'_ = gMul
    x : GroupSyntax 2
    x = inner (zero-Fin)
    y : GroupSyntax 2
    y = inner (succ-Fin zero-Fin)

    infixl 20 _*'_
    ex1 : GroupEquality {n = 2} (gInv (x *' y *' gInv x *' gInv y)) (y *' (x *' (gInv y *' (gInv x *' gUnit))))
    ex1 = simplifyValid _

    _ : GroupEquality {n = 2} (y *' (x *' (gInv y *' (gInv x *' gUnit)))) (y *' (x *' (gInv y *' (gInv x *' gUnit))))
    _ = {!simplifyValid (x *' gUnit)!}
    -- _ = {!simplifyValid (y *' (x *' (gInv y *' (gInv x *' gUnit))))!}
```
