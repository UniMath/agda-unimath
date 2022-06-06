{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdistanceZ45ZnaturalZ45Znumbers where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QinequalityZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes

-- elementary-number-theory.distance-natural-numbers.dist-ℕ
d_dist'45'ℕ_4 :: Integer -> Integer -> Integer
d_dist'45'ℕ_4 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           case coe v1 of
             0 -> coe v0
             _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe d_dist'45'ℕ_4 (coe v2) (coe v3)
-- elementary-number-theory.distance-natural-numbers.dist-ℕ'
d_dist'45'ℕ''_14 :: Integer -> Integer -> Integer
d_dist'45'ℕ''_14 v0 v1 = coe d_dist'45'ℕ_4 (coe v1) (coe v0)
-- elementary-number-theory.distance-natural-numbers.ap-dist-ℕ
d_ap'45'dist'45'ℕ_28 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_ap'45'dist'45'ℕ_28 = erased
-- elementary-number-theory.distance-natural-numbers.eq-dist-ℕ
d_eq'45'dist'45'ℕ_38 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'dist'45'ℕ_38 = erased
-- elementary-number-theory.distance-natural-numbers.dist-eq-ℕ'
d_dist'45'eq'45'ℕ''_50 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_dist'45'eq'45'ℕ''_50 = erased
-- elementary-number-theory.distance-natural-numbers.dist-eq-ℕ
d_dist'45'eq'45'ℕ_58 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_dist'45'eq'45'ℕ_58 = erased
-- elementary-number-theory.distance-natural-numbers.is-one-dist-succ-ℕ
d_is'45'one'45'dist'45'succ'45'ℕ_64 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'one'45'dist'45'succ'45'ℕ_64 = erased
-- elementary-number-theory.distance-natural-numbers.is-one-dist-succ-ℕ'
d_is'45'one'45'dist'45'succ'45'ℕ''_70 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'one'45'dist'45'succ'45'ℕ''_70 = erased
-- elementary-number-theory.distance-natural-numbers.symmetric-dist-ℕ
d_symmetric'45'dist'45'ℕ_78 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_symmetric'45'dist'45'ℕ_78 = erased
-- elementary-number-theory.distance-natural-numbers.left-unit-law-dist-ℕ
d_left'45'unit'45'law'45'dist'45'ℕ_90 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'unit'45'law'45'dist'45'ℕ_90 = erased
-- elementary-number-theory.distance-natural-numbers.right-unit-law-dist-ℕ
d_right'45'unit'45'law'45'dist'45'ℕ_96 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'unit'45'law'45'dist'45'ℕ_96 = erased
-- elementary-number-theory.distance-natural-numbers.triangle-inequality-dist-ℕ
d_triangle'45'inequality'45'dist'45'ℕ_106 ::
  Integer -> Integer -> Integer -> AgdaAny
d_triangle'45'inequality'45'dist'45'ℕ_106 = erased
-- elementary-number-theory.distance-natural-numbers.is-additive-right-inverse-dist-ℕ
d_is'45'additive'45'right'45'inverse'45'dist'45'ℕ_136 ::
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'additive'45'right'45'inverse'45'dist'45'ℕ_136 = erased
-- elementary-number-theory.distance-natural-numbers.triangle-equality-dist-ℕ
d_triangle'45'equality'45'dist'45'ℕ_154 ::
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_triangle'45'equality'45'dist'45'ℕ_154 = erased
-- elementary-number-theory.distance-natural-numbers.rewrite-left-add-dist-ℕ
d_rewrite'45'left'45'add'45'dist'45'ℕ_184 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_rewrite'45'left'45'add'45'dist'45'ℕ_184 = erased
-- elementary-number-theory.distance-natural-numbers.rewrite-left-dist-add-ℕ
d_rewrite'45'left'45'dist'45'add'45'ℕ_200 ::
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_rewrite'45'left'45'dist'45'add'45'ℕ_200 = erased
-- elementary-number-theory.distance-natural-numbers.rewrite-right-add-dist-ℕ
d_rewrite'45'right'45'add'45'dist'45'ℕ_214 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_rewrite'45'right'45'add'45'dist'45'ℕ_214 = erased
-- elementary-number-theory.distance-natural-numbers.rewrite-right-dist-add-ℕ
d_rewrite'45'right'45'dist'45'add'45'ℕ_230 ::
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_rewrite'45'right'45'dist'45'add'45'ℕ_230 = erased
-- elementary-number-theory.distance-natural-numbers.leq-dist-ℕ
d_leq'45'dist'45'ℕ_242 :: Integer -> Integer -> AgdaAny -> AgdaAny
d_leq'45'dist'45'ℕ_242 = erased
-- elementary-number-theory.distance-natural-numbers.translation-invariant-dist-ℕ
d_translation'45'invariant'45'dist'45'ℕ_262 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_translation'45'invariant'45'dist'45'ℕ_262 = erased
-- elementary-number-theory.distance-natural-numbers.translation-invariant-dist-ℕ'
d_translation'45'invariant'45'dist'45'ℕ''_280 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_translation'45'invariant'45'dist'45'ℕ''_280 = erased
-- elementary-number-theory.distance-natural-numbers.left-distributive-mul-dist-ℕ
d_left'45'distributive'45'mul'45'dist'45'ℕ_294 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'distributive'45'mul'45'dist'45'ℕ_294 = erased
-- elementary-number-theory.distance-natural-numbers.right-distributive-mul-dist-ℕ
d_right'45'distributive'45'mul'45'dist'45'ℕ_326 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'distributive'45'mul'45'dist'45'ℕ_326 = erased
-- elementary-number-theory.distance-natural-numbers.is-difference-dist-ℕ
d_is'45'difference'45'dist'45'ℕ_338 ::
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'difference'45'dist'45'ℕ_338 = erased
-- elementary-number-theory.distance-natural-numbers.is-difference-dist-ℕ'
d_is'45'difference'45'dist'45'ℕ''_356 ::
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'difference'45'dist'45'ℕ''_356 = erased
-- elementary-number-theory.distance-natural-numbers.cases-dist-ℕ
d_cases'45'dist'45'ℕ_370 :: Integer -> Integer -> Integer -> ()
d_cases'45'dist'45'ℕ_370 = erased
-- elementary-number-theory.distance-natural-numbers.is-total-dist-ℕ
d_is'45'total'45'dist'45'ℕ_384 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'total'45'dist'45'ℕ_384 v0 v1 v2
  = let v3
          = MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QinequalityZ45ZnaturalZ45Znumbers.d_order'45'three'45'elements'45'ℕ_438
              (coe v0) (coe v1) (coe v2) in
    case coe v3 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v4
        -> case coe v4 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v5
               -> coe
                    seq (coe v5)
                    (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased)
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v5
               -> coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                       (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v4
        -> case coe v4 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v5
               -> case coe v5 of
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v6
                      -> coe
                           seq (coe v6)
                           (coe
                              MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                              (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased))
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v6
                      -> coe
                           seq (coe v6)
                           (coe
                              MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                              (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v5
               -> case coe v5 of
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v6
                      -> coe
                           seq (coe v6)
                           (coe
                              MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                              (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased))
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v6
                      -> coe
                           seq (coe v6)
                           (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.distance-natural-numbers.strict-upper-bound-dist-ℕ
d_strict'45'upper'45'bound'45'dist'45'ℕ_462 ::
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_strict'45'upper'45'bound'45'dist'45'ℕ_462 = erased
